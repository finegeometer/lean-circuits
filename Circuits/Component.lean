import «Circuits».Circuit
import Mathlib.Analysis.Calculus.Deriv.Add

-- In `«Circuits».Circuit`, it was unimportant whether the current values
-- represented the currents *into* or *out of* the circuit.
-- Here, it matters, so I standardize on "into".

namespace Component

--------------------------------------------------------------------------------
-- Standard components.

def resistor (R : ℝ) : Circuit Bool :=
  {bhvr | ∀ t,
    (bhvr true t).2 + (bhvr false t).2 = 0 ∧
    (bhvr true t).2 * R = (bhvr true t).1 - (bhvr false t).1
  }

def capacitor (C : ℝ) : Circuit Bool :=
  {bhvr | ∀ t,
    (bhvr true t).2 + (bhvr false t).2 = 0 ∧
    HasDerivAt (fun t => C * ((bhvr true t).1 - (bhvr false t).1)) (bhvr true t).2 t
  }

def inductor (L : ℝ) : Circuit Bool :=
  {bhvr | ∀ t,
    (bhvr true t).2 + (bhvr false t).2 = 0 ∧
    HasDerivAt (fun t => L * (bhvr true t).2) ((bhvr true t).1 - (bhvr false t).1) t
  }

def transistor (threshhold strength : ℝ) : Circuit (Option Bool) :=
  {bhvr | ∀ t,
    (bhvr none t).2 = 0 ∧
    (bhvr (some true) t).2 + (bhvr (some false) t).2 = 0 ∧
    (bhvr (some false) t).2 = strength * (
      (max ((bhvr none t).1 - (bhvr (some true) t).1 - threshhold) 0)^2 -
      (max ((bhvr none t).1 - (bhvr (some false) t).1 - threshhold) 0)^2
    )
  }

--------------------------------------------------------------------------------
-- Theorems.

def Equiv.boolComm : Bool ≃ Bool := ⟨not, not, Bool.not_not, Bool.not_not⟩

def symm {α : 𝔽} (c : Circuit α) (perm : α ≃ α) : Prop :=
  c = c.map (𝔽.Cospan.ofEquiv perm)

lemma symm.involutive {c : Circuit α} {perm : α ≃ α} (involutive : Function.Involutive perm) :
  (∀ bhvr, bhvr ∈ c → bhvr ∘ perm ∈ c) → symm c perm
:= by
  intro H
  unfold symm Circuit; rw [Circuit.map_ofEquiv]; ext bhvr
  simp only [id_eq, Set.mem_preimage]
  constructor
  · apply H
  · intro pf; have:= H _ pf
    simp [Function.comp.assoc, involutive] at this
    exact this

theorem resistor_symm : symm (resistor R) Equiv.boolComm := by
  apply symm.involutive; exact Bool.not_not
  intro bhvr H t; specialize H t
  constructor; rw [add_comm]; exact H.1
  simp [Equiv.boolComm]
  have: R * ((bhvr true t).2 + (bhvr false t).2) = 0 := by simp [H.1]
  ring_nf at this; linarith [this, H.2]

theorem capacitor_symm : symm (capacitor C) Equiv.boolComm := by
  apply symm.involutive; exact Bool.not_not
  intro bhvr H t; specialize H t
  constructor; rw [add_comm]; exact H.1
  simp [Equiv.boolComm]
  have: (bhvr false t).2 = -(bhvr true t).2 := by linarith [H.1]
  rw [this]
  have: (fun t => C * ((bhvr false t).1 - (bhvr true t).1)) = (fun t => -(C * ((bhvr true t).1 - (bhvr false t).1))) := by funext; ring_nf
  rw [this]
  apply HasDerivAt.neg; exact H.2

theorem inductor_symm : symm (inductor L) Equiv.boolComm := by
  apply symm.involutive; exact Bool.not_not
  intro bhvr H t
  constructor; rw [add_comm]; exact (H t).1
  simp [Equiv.boolComm]
  have: (fun t => L * (bhvr false t).2) = (fun t => -(L * (bhvr true t).2)) := by {
    funext t
    have: L * ((bhvr true t).2 + (bhvr false t).2) = 0 := by simp [(H t).1]
    ring_nf at this; linarith [this]
  }
  rw [this, <-neg_sub]
  apply HasDerivAt.neg; exact (H t).2

theorem transistor_symm : symm (transistor threshhold strength) (Equiv.optionCongr Equiv.boolComm) := by
  apply symm.involutive
  { intro; simp [Equiv.optionCongr, Equiv.boolComm]; eta_expand; simp [Bool.not_not] }
  intro bhvr H t; specialize (H t)
  constructor; exact H.1
  constructor; rw [add_comm]; exact H.2.1
  simp [Equiv.boolComm]
  rw [<-neg_sub, mul_neg, <-H.2.2]
  linarith [H.1]
