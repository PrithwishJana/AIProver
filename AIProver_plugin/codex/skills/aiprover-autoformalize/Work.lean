import Mathlib

structure ManySortedSignature (S : Type) where
  Op : Type
  arity : Op → List S
  resultSort : Op → S

variable (S : Type) (X : S → Type) (Sig : ManySortedSignature S)

inductive Term : S → Type
  | root (s : S) (x : X s) : Term s
  | node (o : Sig.Op) (p : (i : Fin (Sig.arity o).length) → Term ((Sig.arity o).get ⟨i.1, i.2⟩)) : Term (Sig.resultSort o)

-- Can we state the theorem?
example (F : (s : S) → Term S X Sig s → Term S (fun _ => Nat) Sig s)
    (w : (s : S) → X s → Nat)
    (h_root : ∀ (s : S) (x : X s), F s (.root s x) = .root s (w s x))
    (h_node : ∀ (o : Sig.Op)
      (p : (i : Fin (Sig.arity o).length) → Term S X Sig ((Sig.arity o).get ⟨i.1, i.2⟩)),
      F (Sig.resultSort o) (.node o p) =
        .node (X := fun _ : S => Nat) o (fun i => F ((Sig.arity o).get ⟨i.1, i.2⟩) (p i)))) :
    True := by
  trivial