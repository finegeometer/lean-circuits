import «Circuits».Circuit.Directed

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
-- Single-terminal components.

def voltageSource (V : ℝ) : Circuit.Directed Empty Unit :=
  {bhvr | ∀ t, (bhvr (Sum.inr ()) t).1 = V}

def currentSource (I : ℝ) : Circuit.Directed Empty Unit :=
  {bhvr | ∀ t, (bhvr (Sum.inr ()) t).2 = -I}

def pull (V R : ℝ) : Circuit.Directed Empty Unit :=
  {bhvr | ∀ t, (bhvr (Sum.inr ()) t).2 * R = (bhvr (Sum.inr ()) t).1 - V}

def capacitate (C : ℝ) : Circuit.Directed Empty Unit :=
  {bhvr | ∀ t, HasDerivAt (fun t => C * (bhvr (Sum.inr ()) t).1) (bhvr (Sum.inr ()) t).2 t}
