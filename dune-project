(lang dune 3.13)
(wrapped_executables false)
(map_workspace_root false)

(name prototyp)

(generate_opam_files true)

(source
 (github Foxinio/type-inference))

(authors "Szymon Jędras")

(maintainers "Szymon Jędras")

(license MIT)

(package
 (name prototyp)
 (synopsis "Argument folding analysis prototype")
 (description "A longer description")
 (depends ocaml dune))
