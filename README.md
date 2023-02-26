# vSequent

The sequent calculus is a formal proof system for proving logical theorems ([wikipedia](https://en.wikipedia.org/wiki/Sequent_calculus)). Currently this is a proof system for truth-valued propositional logic.

Goals for properties I'd like to prove:
- [ ] **Safety**: applying the inference rules does not change the boolean valuation of the statement.
- [ ] **Termination**: the algorithm will always terminate in a finite number of steps.
- [ ] **Soundness**: if the algorithm says that a statement is a theorem, then it is actually a theorem.
- [ ] **Completeness**: if a statement is actually a theorem, then the algorithm will conclude that it is a theorem.
