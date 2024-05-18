(lang dune 3.15)

(name outside-in)

(generate_opam_files true)

(source
 (github purefunctor/outside-in))

(authors "Justin Garcia")

(maintainers "Justin Garcia")

(license LICENSE)

(package
 (name outside-in)
 (synopsis "An implementation of OutsideIn(X)")
 (description "An implementation of OutsideIn(X).")
 (depends 
  ocaml 
  dune
  (fmt (>= "0.9.0"))
  (logs (>= "0.7.0"))
  (pprint (>= "20230830"))))
