use std::borrow::Cow;
use std::collections::BTreeMap;

pub use serde_json::Value as Json;
use serde_json::{Map, Number};

use rustc_target::spec::abi::Abi;
use rustc_target::spec::crt_objects::LinkSelfContainedDefault;
use rustc_target::spec::*;

pub trait ToJson {
    fn to_json(&self) -> Json;
}

impl ToJson for Json {
    fn to_json(&self) -> Json {
        self.clone()
    }
}

macro_rules! to_json_impl_num {
    ($($t:ty), +) => (
        $(impl ToJson for $t {
            fn to_json(&self) -> Json {
                Json::Number(Number::from(*self))
            }
        })+
    )
}

to_json_impl_num! { isize, i8, i16, i32, i64, usize, u8, u16, u32, u64 }

impl ToJson for bool {
    fn to_json(&self) -> Json {
        Json::Bool(*self)
    }
}

impl ToJson for str {
    fn to_json(&self) -> Json {
        Json::String(self.to_owned())
    }
}

impl ToJson for String {
    fn to_json(&self) -> Json {
        Json::String(self.to_owned())
    }
}

impl<'a> ToJson for Cow<'a, str> {
    fn to_json(&self) -> Json {
        Json::String(self.to_string())
    }
}

impl<A: ToJson> ToJson for [A] {
    fn to_json(&self) -> Json {
        Json::Array(self.iter().map(|elt| elt.to_json()).collect())
    }
}

impl<A: ToJson> ToJson for Vec<A> {
    fn to_json(&self) -> Json {
        Json::Array(self.iter().map(|elt| elt.to_json()).collect())
    }
}

impl<'a, A: ToJson> ToJson for Cow<'a, [A]>
where
    [A]: ToOwned,
{
    fn to_json(&self) -> Json {
        Json::Array(self.iter().map(|elt| elt.to_json()).collect())
    }
}

impl<T: ToString, A: ToJson> ToJson for BTreeMap<T, A> {
    fn to_json(&self) -> Json {
        let mut d = Map::new();
        for (key, value) in self {
            d.insert(key.to_string(), value.to_json());
        }
        Json::Object(d)
    }
}

impl<A: ToJson> ToJson for Option<A> {
    fn to_json(&self) -> Json {
        match *self {
            None => Json::Null,
            Some(ref value) => value.to_json(),
        }
    }
}

impl ToJson for rustc_target::abi::call::Conv {
    fn to_json(&self) -> Json {
        let s = match self {
            Self::C => "C",
            Self::Rust => "Rust",
            Self::RustCold => "RustCold",
            Self::ArmAapcs => "ArmAapcs",
            Self::CCmseNonSecureCall => "CCmseNonSecureCall",
            Self::Msp430Intr => "Msp430Intr",
            Self::PtxKernel => "PtxKernel",
            Self::X86Fastcall => "X86Fastcall",
            Self::X86Intr => "X86Intr",
            Self::X86Stdcall => "X86Stdcall",
            Self::X86ThisCall => "X86ThisCall",
            Self::X86VectorCall => "X86VectorCall",
            Self::X86_64SysV => "X86_64SysV",
            Self::X86_64Win64 => "X86_64Win64",
            Self::AmdGpuKernel => "AmdGpuKernel",
            Self::AvrInterrupt => "AvrInterrupt",
            Self::AvrNonBlockingInterrupt => "AvrNonBlockingInterrupt",
        };
        Json::String(s.to_owned())
    }
}

impl ToJson for Target {
    fn to_json(&self) -> Json {
        let mut d = serde_json::Map::new();
        let default: TargetOptions = Default::default();
        let mut target = self.clone();
        target.update_to_cli();

        macro_rules! target_val {
            ($attr:ident) => {{
                let name = (stringify!($attr)).replace("_", "-");
                d.insert(name, target.$attr.to_json());
            }};
        }

        macro_rules! target_option_val {
            ($attr:ident) => {{
                let name = (stringify!($attr)).replace("_", "-");
                if default.$attr != target.$attr {
                    d.insert(name, target.$attr.to_json());
                }
            }};
            ($attr:ident, $json_name:expr) => {{
                let name = $json_name;
                if default.$attr != target.$attr {
                    d.insert(name.into(), target.$attr.to_json());
                }
            }};
            (link_args - $attr:ident, $json_name:expr) => {{
                let name = $json_name;
                if default.$attr != target.$attr {
                    let obj = target
                        .$attr
                        .iter()
                        .map(|(k, v)| (k.desc().to_string(), v.clone()))
                        .collect::<BTreeMap<_, _>>();
                    d.insert(name.to_string(), obj.to_json());
                }
            }};
            (env - $attr:ident) => {{
                let name = (stringify!($attr)).replace("_", "-");
                if default.$attr != target.$attr {
                    let obj = target
                        .$attr
                        .iter()
                        .map(|&(ref k, ref v)| format!("{k}={v}"))
                        .collect::<Vec<_>>();
                    d.insert(name, obj.to_json());
                }
            }};
        }

        target_val!(llvm_target);
        d.insert("target-pointer-width".to_string(), self.pointer_width.to_string().to_json());
        target_val!(arch);
        target_val!(data_layout);

        target_option_val!(is_builtin);
        target_option_val!(endian, "target-endian");
        target_option_val!(c_int_width, "target-c-int-width");
        target_option_val!(os);
        target_option_val!(env);
        target_option_val!(abi);
        target_option_val!(vendor);
        target_option_val!(linker);
        target_option_val!(linker_flavor_json, "linker-flavor");
        target_option_val!(lld_flavor_json, "lld-flavor");
        target_option_val!(linker_is_gnu_json, "linker-is-gnu");
        target_option_val!(pre_link_objects);
        target_option_val!(post_link_objects);
        target_option_val!(pre_link_objects_self_contained, "pre-link-objects-fallback");
        target_option_val!(post_link_objects_self_contained, "post-link-objects-fallback");
        target_option_val!(link_self_contained, "crt-objects-fallback");
        target_option_val!(link_args - pre_link_args_json, "pre-link-args");
        target_option_val!(link_args - late_link_args_json, "late-link-args");
        target_option_val!(link_args - late_link_args_dynamic_json, "late-link-args-dynamic");
        target_option_val!(link_args - late_link_args_static_json, "late-link-args-static");
        target_option_val!(link_args - post_link_args_json, "post-link-args");
        target_option_val!(link_script);
        target_option_val!(env - link_env);
        target_option_val!(link_env_remove);
        target_option_val!(asm_args);
        target_option_val!(cpu);
        target_option_val!(features);
        target_option_val!(dynamic_linking);
        target_option_val!(dll_tls_export);
        target_option_val!(only_cdylib);
        target_option_val!(executables);
        target_option_val!(relocation_model);
        target_option_val!(code_model);
        target_option_val!(tls_model);
        target_option_val!(disable_redzone);
        target_option_val!(frame_pointer);
        target_option_val!(function_sections);
        target_option_val!(dll_prefix);
        target_option_val!(dll_suffix);
        target_option_val!(exe_suffix);
        target_option_val!(staticlib_prefix);
        target_option_val!(staticlib_suffix);
        target_option_val!(families, "target-family");
        target_option_val!(abi_return_struct_as_int);
        target_option_val!(is_like_aix);
        target_option_val!(is_like_osx);
        target_option_val!(is_like_solaris);
        target_option_val!(is_like_windows);
        target_option_val!(is_like_msvc);
        target_option_val!(is_like_wasm);
        target_option_val!(is_like_android);
        target_option_val!(default_dwarf_version);
        target_option_val!(allows_weak_linkage);
        target_option_val!(has_rpath);
        target_option_val!(no_default_libraries);
        target_option_val!(position_independent_executables);
        target_option_val!(static_position_independent_executables);
        target_option_val!(needs_plt);
        target_option_val!(relro_level);
        target_option_val!(archive_format);
        target_option_val!(allow_asm);
        target_option_val!(main_needs_argc_argv);
        target_option_val!(has_thread_local);
        target_option_val!(obj_is_bitcode);
        target_option_val!(forces_embed_bitcode);
        target_option_val!(bitcode_llvm_cmdline);
        target_option_val!(min_atomic_width);
        target_option_val!(max_atomic_width);
        target_option_val!(atomic_cas);
        target_option_val!(panic_strategy);
        target_option_val!(crt_static_allows_dylibs);
        target_option_val!(crt_static_default);
        target_option_val!(crt_static_respected);
        target_option_val!(stack_probes);
        target_option_val!(min_global_align);
        target_option_val!(default_codegen_units);
        target_option_val!(trap_unreachable);
        target_option_val!(requires_lto);
        target_option_val!(singlethread);
        target_option_val!(no_builtins);
        target_option_val!(default_hidden_visibility);
        target_option_val!(emit_debug_gdb_scripts);
        target_option_val!(requires_uwtable);
        target_option_val!(default_uwtable);
        target_option_val!(simd_types_indirect);
        target_option_val!(limit_rdylib_exports);
        target_option_val!(override_export_symbols);
        target_option_val!(merge_functions);
        target_option_val!(mcount, "target-mcount");
        target_option_val!(llvm_abiname);
        target_option_val!(relax_elf_relocations);
        target_option_val!(llvm_args);
        target_option_val!(use_ctors_section);
        target_option_val!(eh_frame_header);
        target_option_val!(has_thumb_interworking);
        target_option_val!(debuginfo_kind);
        target_option_val!(split_debuginfo);
        target_option_val!(supported_split_debuginfo);
        target_option_val!(supported_sanitizers);
        target_option_val!(c_enum_min_bits);
        target_option_val!(generate_arange_section);
        target_option_val!(supports_stack_protector);
        target_option_val!(entry_name);
        target_option_val!(entry_abi);
        target_option_val!(supports_xray);
        target_option_val!(force_emulated_tls);

        if let Some(abi) = self.default_adjusted_cabi {
            d.insert("default-adjusted-cabi".into(), Abi::name(abi).to_json());
        }

        Json::Object(d)
    }
}

impl ToJson for rustc_target::abi::Endian {
    fn to_json(&self) -> Json {
        self.as_str().to_json()
    }
}

impl ToJson for LldFlavor {
    fn to_json(&self) -> Json {
        self.as_str().to_json()
    }
}

impl ToJson for LinkerFlavorCli {
    fn to_json(&self) -> Json {
        self.desc().to_json()
    }
}

impl ToJson for PanicStrategy {
    fn to_json(&self) -> Json {
        match *self {
            PanicStrategy::Abort => "abort".to_json(),
            PanicStrategy::Unwind => "unwind".to_json(),
        }
    }
}

impl ToJson for RelroLevel {
    fn to_json(&self) -> Json {
        match *self {
            RelroLevel::Full => "full".to_json(),
            RelroLevel::Partial => "partial".to_json(),
            RelroLevel::Off => "off".to_json(),
            RelroLevel::None => "None".to_json(),
        }
    }
}

impl ToJson for MergeFunctions {
    fn to_json(&self) -> Json {
        match *self {
            MergeFunctions::Disabled => "disabled".to_json(),
            MergeFunctions::Trampolines => "trampolines".to_json(),
            MergeFunctions::Aliases => "aliases".to_json(),
        }
    }
}

impl ToJson for RelocModel {
    fn to_json(&self) -> Json {
        match *self {
            RelocModel::Static => "static",
            RelocModel::Pic => "pic",
            RelocModel::Pie => "pie",
            RelocModel::DynamicNoPic => "dynamic-no-pic",
            RelocModel::Ropi => "ropi",
            RelocModel::Rwpi => "rwpi",
            RelocModel::RopiRwpi => "ropi-rwpi",
        }
        .to_json()
    }
}

impl ToJson for CodeModel {
    fn to_json(&self) -> Json {
        match *self {
            CodeModel::Tiny => "tiny",
            CodeModel::Small => "small",
            CodeModel::Kernel => "kernel",
            CodeModel::Medium => "medium",
            CodeModel::Large => "large",
        }
        .to_json()
    }
}

impl ToJson for TlsModel {
    fn to_json(&self) -> Json {
        match *self {
            TlsModel::GeneralDynamic => "global-dynamic",
            TlsModel::LocalDynamic => "local-dynamic",
            TlsModel::InitialExec => "initial-exec",
            TlsModel::LocalExec => "local-exec",
        }
        .to_json()
    }
}

impl ToJson for DebuginfoKind {
    fn to_json(&self) -> Json {
        self.as_str().to_json()
    }
}

impl ToJson for SplitDebuginfo {
    fn to_json(&self) -> Json {
        self.as_str().to_json()
    }
}

impl ToJson for SanitizerSet {
    fn to_json(&self) -> Json {
        self.into_iter()
            .map(|v| Some(v.as_str()?.to_json()))
            .collect::<Option<Vec<_>>>()
            .unwrap_or_default()
            .to_json()
    }
}

impl ToJson for FramePointer {
    fn to_json(&self) -> Json {
        match *self {
            Self::Always => "always",
            Self::NonLeaf => "non-leaf",
            Self::MayOmit => "may-omit",
        }
        .to_json()
    }
}

impl ToJson for LinkSelfContainedDefault {
    fn to_json(&self) -> Json {
        match *self {
            LinkSelfContainedDefault::False => "false",
            LinkSelfContainedDefault::True => "true",
            LinkSelfContainedDefault::Musl => "musl",
            LinkSelfContainedDefault::Mingw => "mingw",
        }
        .to_json()
    }
}
