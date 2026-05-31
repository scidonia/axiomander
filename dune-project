(lang dune 3.21)
(using rocq 0.11)

(name axiomander)
(package
  (name axiomander)
  (synopsis "Hoare-logic verification pipeline for Python")
  (depends (rocq-core (>= 9.0.0)) (rocq-stdlib (>= 9.0.0))))
