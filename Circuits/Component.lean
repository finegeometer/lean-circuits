import «Circuits».Circuit.Directed
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

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

--------------------------------------------------------------------------------
-- Single-terminal components.

def voltageSource (V : ℝ) : Circuit.Directed Empty Unit :=
  {bhvr | ∀ t, (bhvr (Sum.inr ()) t).1 = V}

def currentSource (I : ℝ) : Circuit.Directed Empty Unit :=
  {bhvr | ∀ t, (bhvr (Sum.inr ()) t).2 = -I}

def pull (V R : ℝ) : Circuit.Directed Empty Unit :=
  {bhvr | ∀ t, (bhvr (Sum.inr ()) t).2 * R = (bhvr (Sum.inr ()) t).1 - V}

def capacitate (C : ℝ) : Circuit.Directed Empty Unit :=
  {bhvr | ∀ t, HasDerivAt (fun t => C * (bhvr (Sum.inr ()) t).1) (bhvr (Sum.inr ()) t).2 t}

--------------------------------------------------------------------------------
-- Theorems.

theorem pull_spec : pull V R = (voltageSource V).comp (resistor R) := by
  ext input output
  simp [Circuit.Directed.mem_comp]
  constructor
  · intro H
    exists fun () t => (V, (output () t).2)
    constructor
    · intro t; rfl
    · intro t; simp
      specialize H t; simp at H
      linarith [H]
  · intro ⟨middle,H1,H2⟩ t; simp
    specialize H1 t; specialize H2 t; obtain ⟨H2,H3⟩ := H2
    simp at H1 H2 H3
    calc -((output () t).2 * R)
      _ = -((middle () t).2 * R) := by congr 2; linarith [H2]
      _ = (output () t).1 - V := by rw [H3, H1]; linarith

theorem capacitate_spec : capacitate C = (voltageSource V).comp (capacitor C) := by
  ext input output
  simp [Circuit.Directed.mem_comp]
  constructor
  · intro H
    exists fun () t => (V, (output () t).2)
    constructor
    · intro t; rfl
    · intro t; simp [mul_sub]
      have:= HasDerivAt.const_sub (C * V) (H t)
      simp at this; exact this
  · intro ⟨middle,H1,H2⟩ t; simp
    specialize H2 t; obtain ⟨H2,H3⟩ := H2
    simp at H2 H3

    have H3 := HasDerivAt.const_sub (C * V) H3

    have: (-(middle () t).2) = (-(output () t).2) := by linarith [H2]
    rw [this] at H3

    have: (fun t => C * V - C * ((middle () t).1 - (output () t).1)) = (fun t => C * (output () t).1) := by
      funext t
      have:= H1 t; simp at this; rw [this]
      ring_nf
    rw [this] at H3

    exact H3
