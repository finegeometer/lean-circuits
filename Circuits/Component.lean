import «Circuits».Circuit.Directed
import Mathlib.Analysis.Calculus.Deriv.Add

-- In `«Circuits».Circuit`, it was unimportant whether the current values
-- represented the currents *into* or *out of* the circuit.
-- Here, it matters, so I standardize on "into".

namespace Component

--------------------------------------------------------------------------------
-- Standard components.

def resistor (R : ℝ) : Circuit.Directed Unit Unit :=
  {bhvr | ∀ t,
    (bhvr (Sum.inl ()) t).2 + (bhvr (Sum.inr ()) t).2 = 0 ∧
    (bhvr (Sum.inl ()) t).2 * R = (bhvr (Sum.inl ()) t).1 - (bhvr (Sum.inr ()) t).1
  }

def capacitor (C : ℝ) : Circuit.Directed Unit Unit :=
  {bhvr | ∀ t,
    (bhvr (Sum.inl ()) t).2 + (bhvr (Sum.inr ()) t).2 = 0 ∧
    HasDerivAt (fun t => C * ((bhvr (Sum.inl ()) t).1 - (bhvr (Sum.inr ()) t).1)) (bhvr (Sum.inl ()) t).2 t
  }

def inductor (L : ℝ) : Circuit.Directed Unit Unit :=
  {bhvr | ∀ t,
    (bhvr (Sum.inl ()) t).2 + (bhvr (Sum.inr ()) t).2 = 0 ∧
    HasDerivAt (fun t => L * (bhvr (Sum.inl ()) t).2) ((bhvr (Sum.inl ()) t).1 - (bhvr (Sum.inr ()) t).1) t
  }

def transistor (threshhold strength : ℝ) : Circuit.Directed Unit Bool :=
  {bhvr | ∀ t,
    (bhvr (Sum.inl ()) t).2 = 0 ∧
    (bhvr (Sum.inr true) t).2 + (bhvr (Sum.inr false) t).2 = 0 ∧
    (bhvr (Sum.inr false) t).2 = strength * (
      (max ((bhvr (Sum.inl ()) t).1 - (bhvr (Sum.inr true) t).1 - threshhold) 0)^2 -
      (max ((bhvr (Sum.inl ()) t).1 - (bhvr (Sum.inr false) t).1 - threshhold) 0)^2
    )
  }

--------------------------------------------------------------------------------
-- Theorems.

private lemma symm (c : Circuit.Directed α α) : by
  let c' := c.reverse
  unfold Circuit.Directed at c c'
  exact (∀ x, x ∈ c → x ∘ Sum.swap ∈ c) → c = c'
:= by
  intro c'
  simp only [c', Circuit.Directed.reverse, Circuit.map_ofEquiv, Circuit, Equiv.sumComm_apply, id_eq, Set.mem_preimage]
  intro H; ext bhvr; rw [Set.mem_preimage]
  constructor
  · exact H bhvr
  · intro pf
    have:= H (bhvr ∘ Sum.swap) pf
    simp [Function.comp.assoc] at this; exact this

theorem resistor_symm : (resistor R).reverse = resistor R := by
  symm; apply symm
  intro bhvr H t; specialize H t
  constructor; rw [add_comm]; exact H.1
  simp [Sum.swap]
  have: R * ((bhvr (Sum.inl ()) t).2 + (bhvr (Sum.inr ()) t).2) = 0 := by simp [H.1]
  ring_nf at this; linarith [this, H.2]

theorem capacitor_symm : (capacitor C).reverse = capacitor C := by
  symm; apply symm
  intro bhvr H t; specialize H t
  constructor; rw [add_comm]; exact H.1
  simp [Sum.swap]
  have: (bhvr (Sum.inr ()) t).2 = -(bhvr (Sum.inl ()) t).2 := by linarith [H.1]
  rw [this]
  have: (fun t => C * ((bhvr (Sum.inr ()) t).1 - (bhvr (Sum.inl ()) t).1)) = (fun t => -(C * ((bhvr (Sum.inl ()) t).1 - (bhvr (Sum.inr ()) t).1))) := by funext; ring_nf
  rw [this]
  apply HasDerivAt.neg; exact H.2

theorem inductor_symm : (inductor L).reverse = inductor L := by
  symm; apply symm
  intro bhvr H t
  constructor; rw [add_comm]; exact (H t).1
  simp [Sum.swap]
  have: (fun t => L * (bhvr (Sum.inr ()) t).2) = (fun t => -(L * (bhvr (Sum.inl ()) t).2)) := by {
    funext t
    have: L * ((bhvr (Sum.inl ()) t).2 + (bhvr (Sum.inr ()) t).2) = 0 := by simp [(H t).1]
    ring_nf at this; linarith [this]
  }
  rw [this, <-neg_sub]
  apply HasDerivAt.neg; exact (H t).2
