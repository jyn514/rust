use rustc_target::abi::call::Conv;
use crate::target_json::{Json, ToJson};
use rustc_target::spec::*;
use rustc_target::spec::abi::{lookup as lookup_abi};
use rustc_target::spec::crt_objects::{CrtObjects, LinkSelfContainedDefault};
use std::borrow::Cow;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use rustc_target::spec::Target;

use serde_json::Value;

/// Loads a target descriptor from a JSON object.
pub fn load_json(obj: Json) -> Result<(Target, TargetWarnings), String> {
    // While ugly, this code must remain this way to retain
    // compatibility with existing JSON fields and the internal
    // expected naming of the Target and TargetOptions structs.
    // To ensure compatibility is retained, the built-in targets
    // are round-tripped through this code to catch cases where
    // the JSON parser is not updated to match the structs.

    let mut obj = match obj {
        Value::Object(obj) => obj,
        _ => return Err("Expected JSON object for target")?,
    };

    let mut get_req_field = |name: &str| {
        obj.remove(name)
            .and_then(|j| j.as_str().map(str::to_string))
            .ok_or_else(|| format!("Field {name} in target specification is required"))
    };

    let mut base = Target {
        llvm_target: get_req_field("llvm-target")?.into(),
        pointer_width: get_req_field("target-pointer-width")?
            .parse::<u32>()
            .map_err(|_| "target-pointer-width must be an integer".to_string())?,
        data_layout: get_req_field("data-layout")?.into(),
        arch: get_req_field("arch")?.into(),
        options: Default::default(),
    };

    let mut incorrect_type = vec![];

    macro_rules! key {
        ($key_name:ident) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            if let Some(s) = obj.remove(&name).and_then(|s| s.as_str().map(str::to_string).map(Cow::from)) {
                base.$key_name = s;
            }
        } );
        ($key_name:ident = $json_name:expr) => ( {
            let name = $json_name;
            if let Some(s) = obj.remove(name).and_then(|s| s.as_str().map(str::to_string).map(Cow::from)) {
                base.$key_name = s;
            }
        } );
        ($key_name:ident, bool) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            if let Some(s) = obj.remove(&name).and_then(|b| b.as_bool()) {
                base.$key_name = s;
            }
        } );
        ($key_name:ident = $json_name:expr, bool) => ( {
            let name = $json_name;
            if let Some(s) = obj.remove(name).and_then(|b| b.as_bool()) {
                base.$key_name = s;
            }
        } );
        ($key_name:ident, u32) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            if let Some(s) = obj.remove(&name).and_then(|b| b.as_u64()) {
                if s < 1 || s > 5 {
                    return Err("Not a valid DWARF version number".into());
                }
                base.$key_name = s as u32;
            }
        } );
        ($key_name:ident, Option<u64>) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            if let Some(s) = obj.remove(&name).and_then(|b| b.as_u64()) {
                base.$key_name = Some(s);
            }
        } );
        ($key_name:ident, MergeFunctions) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            obj.remove(&name).and_then(|o| o.as_str().and_then(|s| {
                match s.parse::<MergeFunctions>() {
                    Ok(mergefunc) => base.$key_name = mergefunc,
                    _ => return Some(Err(format!("'{}' is not a valid value for \
                                                    merge-functions. Use 'disabled', \
                                                    'trampolines', or 'aliases'.",
                                                    s))),
                }
                Some(Ok(()))
            })).unwrap_or(Ok(()))
        } );
        ($key_name:ident, RelocModel) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            obj.remove(&name).and_then(|o| o.as_str().and_then(|s| {
                match s.parse::<RelocModel>() {
                    Ok(relocation_model) => base.$key_name = relocation_model,
                    _ => return Some(Err(format!("'{}' is not a valid relocation model. \
                                                    Run `rustc --print relocation-models` to \
                                                    see the list of supported values.", s))),
                }
                Some(Ok(()))
            })).unwrap_or(Ok(()))
        } );
        ($key_name:ident, CodeModel) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            obj.remove(&name).and_then(|o| o.as_str().and_then(|s| {
                match s.parse::<CodeModel>() {
                    Ok(code_model) => base.$key_name = Some(code_model),
                    _ => return Some(Err(format!("'{}' is not a valid code model. \
                                                    Run `rustc --print code-models` to \
                                                    see the list of supported values.", s))),
                }
                Some(Ok(()))
            })).unwrap_or(Ok(()))
        } );
        ($key_name:ident, TlsModel) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            obj.remove(&name).and_then(|o| o.as_str().and_then(|s| {
                match s.parse::<TlsModel>() {
                    Ok(tls_model) => base.$key_name = tls_model,
                    _ => return Some(Err(format!("'{}' is not a valid TLS model. \
                                                    Run `rustc --print tls-models` to \
                                                    see the list of supported values.", s))),
                }
                Some(Ok(()))
            })).unwrap_or(Ok(()))
        } );
        ($key_name:ident, PanicStrategy) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            obj.remove(&name).and_then(|o| o.as_str().and_then(|s| {
                match s {
                    "unwind" => base.$key_name = PanicStrategy::Unwind,
                    "abort" => base.$key_name = PanicStrategy::Abort,
                    _ => return Some(Err(format!("'{}' is not a valid value for \
                                                    panic-strategy. Use 'unwind' or 'abort'.",
                                                    s))),
            }
            Some(Ok(()))
        })).unwrap_or(Ok(()))
        } );
        ($key_name:ident, RelroLevel) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            obj.remove(&name).and_then(|o| o.as_str().and_then(|s| {
                match s.parse::<RelroLevel>() {
                    Ok(level) => base.$key_name = level,
                    _ => return Some(Err(format!("'{}' is not a valid value for \
                                                    relro-level. Use 'full', 'partial, or 'off'.",
                                                    s))),
                }
                Some(Ok(()))
            })).unwrap_or(Ok(()))
        } );
        ($key_name:ident, DebuginfoKind) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            obj.remove(&name).and_then(|o| o.as_str().and_then(|s| {
                match s.parse::<DebuginfoKind>() {
                    Ok(level) => base.$key_name = level,
                    _ => return Some(Err(
                        format!("'{s}' is not a valid value for debuginfo-kind. Use 'dwarf', \
                                'dwarf-dsym' or 'pdb'.")
                    )),
                }
                Some(Ok(()))
            })).unwrap_or(Ok(()))
        } );
        ($key_name:ident, SplitDebuginfo) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            obj.remove(&name).and_then(|o| o.as_str().and_then(|s| {
                match s.parse::<SplitDebuginfo>() {
                    Ok(level) => base.$key_name = level,
                    _ => return Some(Err(format!("'{}' is not a valid value for \
                                                    split-debuginfo. Use 'off' or 'dsymutil'.",
                                                    s))),
                }
                Some(Ok(()))
            })).unwrap_or(Ok(()))
        } );
        ($key_name:ident, list) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            if let Some(j) = obj.remove(&name) {
                if let Some(v) = j.as_array() {
                    base.$key_name = v.iter()
                        .map(|a| a.as_str().unwrap().to_string().into())
                        .collect();
                } else {
                    incorrect_type.push(name)
                }
            }
        } );
        ($key_name:ident, opt_list) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            if let Some(j) = obj.remove(&name) {
                if let Some(v) = j.as_array() {
                    base.$key_name = Some(v.iter()
                        .map(|a| a.as_str().unwrap().to_string().into())
                        .collect());
                } else {
                    incorrect_type.push(name)
                }
            }
        } );
        ($key_name:ident, fallible_list) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            obj.remove(&name).and_then(|j| {
                if let Some(v) = j.as_array() {
                    match v.iter().map(|a| FromStr::from_str(a.as_str().unwrap())).collect() {
                        Ok(l) => { base.$key_name = l },
                        // FIXME: `fallible_list` can't re-use the `key!` macro for list
                        // elements and the error messages from that macro, so it has a bad
                        // generic message instead
                        Err(_) => return Some(Err(
                            format!("`{:?}` is not a valid value for `{}`", j, name)
                        )),
                    }
                } else {
                    incorrect_type.push(name)
                }
                Some(Ok(()))
            }).unwrap_or(Ok(()))
        } );
        ($key_name:ident, optional) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            if let Some(o) = obj.remove(&name) {
                base.$key_name = o
                    .as_str()
                    .map(|s| s.to_string().into());
            }
        } );
        ($key_name:ident = $json_name:expr, LldFlavor) => ( {
            let name = $json_name;
            obj.remove(name).and_then(|o| o.as_str().and_then(|s| {
                if let Some(flavor) = LldFlavor::from_str(&s) {
                    base.$key_name = flavor;
                } else {
                    return Some(Err(format!(
                        "'{}' is not a valid value for lld-flavor. \
                            Use 'darwin', 'gnu', 'link' or 'wasm'.",
                        s)))
                }
                Some(Ok(()))
            })).unwrap_or(Ok(()))
        } );
        ($key_name:ident = $json_name:expr, LinkerFlavor) => ( {
            let name = $json_name;
            obj.remove(name).and_then(|o| o.as_str().and_then(|s| {
                match LinkerFlavorCli::from_str(s) {
                    Some(linker_flavor) => base.$key_name = linker_flavor,
                    _ => return Some(Err(format!("'{}' is not a valid value for linker-flavor. \
                                                    Use {}", s, LinkerFlavorCli::one_of()))),
                }
                Some(Ok(()))
            })).unwrap_or(Ok(()))
        } );
        ($key_name:ident, StackProbeType) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            obj.remove(&name).and_then(|o| match parse_stack_probe_type(&o) {
                Ok(v) => {
                    base.$key_name = v;
                    Some(Ok(()))
                },
                Err(s) => Some(Err(
                    format!("`{:?}` is not a valid value for `{}`: {}", o, name, s)
                )),
            }).unwrap_or(Ok(()))
        } );
        ($key_name:ident, SanitizerSet) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            if let Some(o) = obj.remove(&name) {
                if let Some(a) = o.as_array() {
                    for s in a {
                        base.$key_name |= match s.as_str() {
                            Some("address") => SanitizerSet::ADDRESS,
                            Some("cfi") => SanitizerSet::CFI,
                            Some("kcfi") => SanitizerSet::KCFI,
                            Some("kernel-address") => SanitizerSet::KERNELADDRESS,
                            Some("leak") => SanitizerSet::LEAK,
                            Some("memory") => SanitizerSet::MEMORY,
                            Some("memtag") => SanitizerSet::MEMTAG,
                            Some("shadow-call-stack") => SanitizerSet::SHADOWCALLSTACK,
                            Some("thread") => SanitizerSet::THREAD,
                            Some("hwaddress") => SanitizerSet::HWADDRESS,
                            Some(s) => return Err(format!("unknown sanitizer {}", s)),
                            _ => return Err(format!("not a string: {:?}", s)),
                        };
                    }
                } else {
                    incorrect_type.push(name)
                }
            }
            Ok::<(), String>(())
        } );

        ($key_name:ident = $json_name:expr, link_self_contained) => ( {
            let name = $json_name;
            obj.remove(name).and_then(|o| o.as_str().and_then(|s| {
                match s.parse::<LinkSelfContainedDefault>() {
                    Ok(lsc_default) => base.$key_name = lsc_default,
                    _ => return Some(Err(format!("'{}' is not a valid `-Clink-self-contained` default. \
                                                    Use 'false', 'true', 'musl' or 'mingw'", s))),
                }
                Some(Ok(()))
            })).unwrap_or(Ok(()))
        } );
        ($key_name:ident = $json_name:expr, link_objects) => ( {
            let name = $json_name;
            if let Some(val) = obj.remove(name) {
                let obj = val.as_object().ok_or_else(|| format!("{}: expected a \
                    JSON object with fields per CRT object kind.", name))?;
                let mut args = CrtObjects::new();
                for (k, v) in obj {
                    let kind = LinkOutputKind::from_str(&k).ok_or_else(|| {
                        format!("{}: '{}' is not a valid value for CRT object kind. \
                                    Use '(dynamic,static)-(nopic,pic)-exe' or \
                                    '(dynamic,static)-dylib' or 'wasi-reactor-exe'", name, k)
                    })?;

                    let v = v.as_array().ok_or_else(||
                        format!("{}.{}: expected a JSON array", name, k)
                    )?.iter().enumerate()
                        .map(|(i,s)| {
                            let s = s.as_str().ok_or_else(||
                                format!("{}.{}[{}]: expected a JSON string", name, k, i))?;
                            Ok(s.to_string().into())
                        })
                        .collect::<Result<Vec<_>, String>>()?;

                    args.insert(kind, v);
                }
                base.$key_name = args;
            }
        } );
        ($key_name:ident = $json_name:expr, link_args) => ( {
            let name = $json_name;
            if let Some(val) = obj.remove(name) {
                let obj = val.as_object().ok_or_else(|| format!("{}: expected a \
                    JSON object with fields per linker-flavor.", name))?;
                let mut args = LinkArgsCli::new();
                for (k, v) in obj {
                    let flavor = LinkerFlavorCli::from_str(&k).ok_or_else(|| {
                        format!("{}: '{}' is not a valid value for linker-flavor. \
                                    Use 'em', 'gcc', 'ld' or 'msvc'", name, k)
                    })?;

                    let v = v.as_array().ok_or_else(||
                        format!("{}.{}: expected a JSON array", name, k)
                    )?.iter().enumerate()
                        .map(|(i,s)| {
                            let s = s.as_str().ok_or_else(||
                                format!("{}.{}[{}]: expected a JSON string", name, k, i))?;
                            Ok(s.to_string().into())
                        })
                        .collect::<Result<Vec<_>, String>>()?;

                    args.insert(flavor, v);
                }
                base.$key_name = args;
            }
        } );
        ($key_name:ident, env) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            if let Some(o) = obj.remove(&name) {
                if let Some(a) = o.as_array() {
                    for o in a {
                        if let Some(s) = o.as_str() {
                            let p = s.split('=').collect::<Vec<_>>();
                            if p.len() == 2 {
                                let k = p[0].to_string();
                                let v = p[1].to_string();
                                base.$key_name.to_mut().push((k.into(), v.into()));
                            }
                        }
                    }
                } else {
                    incorrect_type.push(name)
                }
            }
        } );
        ($key_name:ident, Option<Abi>) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            obj.remove(&name).and_then(|o| o.as_str().and_then(|s| {
                match lookup_abi(s) {
                    Some(abi) => base.$key_name = Some(abi),
                    _ => return Some(Err(format!("'{}' is not a valid value for abi", s))),
                }
                Some(Ok(()))
            })).unwrap_or(Ok(()))
        } );
        ($key_name:ident, TargetFamilies) => ( {
            if let Some(value) = obj.remove("target-family") {
                if let Some(v) = value.as_array() {
                    base.$key_name = v.iter()
                        .map(|a| a.as_str().unwrap().to_string().into())
                        .collect();
                } else if let Some(v) = value.as_str() {
                    base.$key_name = vec![v.to_string().into()].into();
                }
            }
        } );
        ($key_name:ident, Conv) => ( {
            let name = (stringify!($key_name)).replace("_", "-");
            obj.remove(&name).and_then(|o| o.as_str().and_then(|s| {
                match Conv::from_str(s) {
                    Ok(c) => {
                        base.$key_name = c;
                        Some(Ok(()))
                    }
                    Err(e) => Some(Err(e))
                }
            })).unwrap_or(Ok(()))
        } );
    }

    if let Some(j) = obj.remove("target-endian") {
        if let Some(s) = j.as_str() {
            base.endian = s.parse()?;
        } else {
            incorrect_type.push("target-endian".into())
        }
    }

    if let Some(fp) = obj.remove("frame-pointer") {
        if let Some(s) = fp.as_str() {
            base.frame_pointer = s
                .parse()
                .map_err(|()| format!("'{s}' is not a valid value for frame-pointer"))?;
        } else {
            incorrect_type.push("frame-pointer".into())
        }
    }

    key!(is_builtin, bool);
    key!(c_int_width = "target-c-int-width");
    key!(c_enum_min_bits, Option<u64>); // if None, matches c_int_width
    key!(os);
    key!(env);
    key!(abi);
    key!(vendor);
    key!(linker, optional);
    key!(linker_flavor_json = "linker-flavor", LinkerFlavor)?;
    key!(lld_flavor_json = "lld-flavor", LldFlavor)?;
    key!(linker_is_gnu_json = "linker-is-gnu", bool);
    key!(pre_link_objects = "pre-link-objects", link_objects);
    key!(post_link_objects = "post-link-objects", link_objects);
    key!(pre_link_objects_self_contained = "pre-link-objects-fallback", link_objects);
    key!(post_link_objects_self_contained = "post-link-objects-fallback", link_objects);
    key!(link_self_contained = "crt-objects-fallback", link_self_contained)?;
    key!(pre_link_args_json = "pre-link-args", link_args);
    key!(late_link_args_json = "late-link-args", link_args);
    key!(late_link_args_dynamic_json = "late-link-args-dynamic", link_args);
    key!(late_link_args_static_json = "late-link-args-static", link_args);
    key!(post_link_args_json = "post-link-args", link_args);
    key!(link_script, optional);
    key!(link_env, env);
    key!(link_env_remove, list);
    key!(asm_args, list);
    key!(cpu);
    key!(features);
    key!(dynamic_linking, bool);
    key!(dll_tls_export, bool);
    key!(only_cdylib, bool);
    key!(executables, bool);
    key!(relocation_model, RelocModel)?;
    key!(code_model, CodeModel)?;
    key!(tls_model, TlsModel)?;
    key!(disable_redzone, bool);
    key!(function_sections, bool);
    key!(dll_prefix);
    key!(dll_suffix);
    key!(exe_suffix);
    key!(staticlib_prefix);
    key!(staticlib_suffix);
    key!(families, TargetFamilies);
    key!(abi_return_struct_as_int, bool);
    key!(is_like_aix, bool);
    key!(is_like_osx, bool);
    key!(is_like_solaris, bool);
    key!(is_like_windows, bool);
    key!(is_like_msvc, bool);
    key!(is_like_wasm, bool);
    key!(is_like_android, bool);
    key!(default_dwarf_version, u32);
    key!(allows_weak_linkage, bool);
    key!(has_rpath, bool);
    key!(no_default_libraries, bool);
    key!(position_independent_executables, bool);
    key!(static_position_independent_executables, bool);
    key!(needs_plt, bool);
    key!(relro_level, RelroLevel)?;
    key!(archive_format);
    key!(allow_asm, bool);
    key!(main_needs_argc_argv, bool);
    key!(has_thread_local, bool);
    key!(obj_is_bitcode, bool);
    key!(forces_embed_bitcode, bool);
    key!(bitcode_llvm_cmdline);
    key!(max_atomic_width, Option<u64>);
    key!(min_atomic_width, Option<u64>);
    key!(atomic_cas, bool);
    key!(panic_strategy, PanicStrategy)?;
    key!(crt_static_allows_dylibs, bool);
    key!(crt_static_default, bool);
    key!(crt_static_respected, bool);
    key!(stack_probes, StackProbeType)?;
    key!(min_global_align, Option<u64>);
    key!(default_codegen_units, Option<u64>);
    key!(trap_unreachable, bool);
    key!(requires_lto, bool);
    key!(singlethread, bool);
    key!(no_builtins, bool);
    key!(default_hidden_visibility, bool);
    key!(emit_debug_gdb_scripts, bool);
    key!(requires_uwtable, bool);
    key!(default_uwtable, bool);
    key!(simd_types_indirect, bool);
    key!(limit_rdylib_exports, bool);
    key!(override_export_symbols, opt_list);
    key!(merge_functions, MergeFunctions)?;
    key!(mcount = "target-mcount");
    key!(llvm_abiname);
    key!(relax_elf_relocations, bool);
    key!(llvm_args, list);
    key!(use_ctors_section, bool);
    key!(eh_frame_header, bool);
    key!(has_thumb_interworking, bool);
    key!(debuginfo_kind, DebuginfoKind)?;
    key!(split_debuginfo, SplitDebuginfo)?;
    key!(supported_split_debuginfo, fallible_list)?;
    key!(supported_sanitizers, SanitizerSet)?;
    key!(default_adjusted_cabi, Option<Abi>)?;
    key!(generate_arange_section, bool);
    key!(supports_stack_protector, bool);
    key!(entry_name);
    key!(entry_abi, Conv)?;
    key!(supports_xray, bool);
    key!(force_emulated_tls, bool);

    if base.is_builtin {
        // This can cause unfortunate ICEs later down the line.
        return Err("may not set is_builtin for targets not built-in".into());
    }
    base.update_from_cli();

    // Each field should have been read using `Json::remove` so any keys remaining are unused.
    let remaining_keys = obj.keys();
    Ok((
        base,
        TargetWarnings { unused_fields: remaining_keys.cloned().collect(), incorrect_type },
    ))
}

/// Search for a JSON file specifying the given target triple.
///
/// If none is found in `$RUST_TARGET_PATH`, look for a file called `target.json` inside the
/// sysroot under the target-triple's `rustlib` directory. Note that it could also just be a
/// bare filename already, so also check for that. If one of the hardcoded targets we know
/// about, just return it directly.
///
/// The error string could come from any of the APIs called, including filesystem access and
/// JSON decoding.
pub fn search(
    target_triple: &TargetTriple,
    sysroot: &Path,
) -> Result<(Target, TargetWarnings), String> {
    use std::env;
    use std::fs;

    fn load_file(path: &Path) -> Result<(Target, TargetWarnings), String> {
        let contents = fs::read_to_string(path).map_err(|e| e.to_string())?;
        let obj = serde_json::from_str(&contents).map_err(|e| e.to_string())?;
        load_json(obj)
    }

    match *target_triple {
        TargetTriple::TargetTriple(ref target_triple) => {
            // check if triple is in list of built-in targets
            if let Some(t) = load_builtin(target_triple) {
                return Ok((t, TargetWarnings::empty()));
            }

            // search for a file named `target_triple`.json in RUST_TARGET_PATH
            let path = {
                let mut target = target_triple.to_string();
                target.push_str(".json");
                PathBuf::from(target)
            };

            let target_path = env::var_os("RUST_TARGET_PATH").unwrap_or_default();

            for dir in env::split_paths(&target_path) {
                let p = dir.join(&path);
                if p.is_file() {
                    return load_file(&p);
                }
            }

            // Additionally look in the sysroot under `lib/rustlib/<triple>/target.json`
            // as a fallback.
            let rustlib_path = rustc_target::target_rustlib_path(sysroot, target_triple);
            let p = PathBuf::from_iter([
                Path::new(sysroot),
                Path::new(&rustlib_path),
                Path::new("target.json"),
            ]);
            if p.is_file() {
                return load_file(&p);
            }

            Err(format!("Could not find specification for target {target_triple:?}"))
        }
        TargetTriple::TargetJson { ref contents, .. } => {
            let obj = serde_json::from_str(contents).map_err(|e| e.to_string())?;
            load_json(obj)
        }
    }
}

impl ToJson for StackProbeType {
    fn to_json(&self) -> Json {
        Json::Object(match self {
            StackProbeType::None => {
                [(String::from("kind"), "none".to_json())].into_iter().collect()
            }
            StackProbeType::Inline => {
                [(String::from("kind"), "inline".to_json())].into_iter().collect()
            }
            StackProbeType::Call => {
                [(String::from("kind"), "call".to_json())].into_iter().collect()
            }
            StackProbeType::InlineOrCall { min_llvm_version_for_inline: (maj, min, patch) } => [
                (String::from("kind"), "inline-or-call".to_json()),
                (
                    String::from("min-llvm-version-for-inline"),
                    Json::Array(vec![maj.to_json(), min.to_json(), patch.to_json()]),
                ),
            ]
            .into_iter()
            .collect(),
        })
    }
}

fn parse_stack_probe_type(json: &Json) -> Result<StackProbeType, String> {
    let object = json.as_object().ok_or_else(|| "expected a JSON object")?;
    let kind = object
        .get("kind")
        .and_then(|o| o.as_str())
        .ok_or_else(|| "expected `kind` to be a string")?;
    match kind {
        "none" => Ok(StackProbeType::None),
        "inline" => Ok(StackProbeType::Inline),
        "call" => Ok(StackProbeType::Call),
        "inline-or-call" => {
            let min_version = object
                .get("min-llvm-version-for-inline")
                .and_then(|o| o.as_array())
                .ok_or_else(|| "expected `min-llvm-version-for-inline` to be an array")?;
            let mut iter = min_version.into_iter().map(|v| {
                let int = v.as_u64().ok_or_else(
                    || "expected `min-llvm-version-for-inline` values to be integers",
                )?;
                u32::try_from(int)
                    .map_err(|_| "`min-llvm-version-for-inline` values don't convert to u32")
            });
            let min_llvm_version_for_inline = (
                iter.next().unwrap_or(Ok(11))?,
                iter.next().unwrap_or(Ok(0))?,
                iter.next().unwrap_or(Ok(0))?,
            );
            Ok(StackProbeType::InlineOrCall { min_llvm_version_for_inline })
        }
        _ => Err(String::from(
            "`kind` expected to be one of `none`, `inline`, `call` or `inline-or-call`",
        )),
    }
}
