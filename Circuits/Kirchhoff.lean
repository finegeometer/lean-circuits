import Mathlib.Analysis.Calculus.Deriv.Basic
import «Circuits».Utils

open Classical
noncomputable local instance (priority := 2000) (α : Type) [Finite α] : Fintype α := Fintype.ofFinite α

-- Kirchhoff's Laws
structure Kirchhoff (f : 𝔽.Cospan α β) (a : α → ℝ × ℝ) (b : β → ℝ × ℝ) : Prop where
  -- The voltages on each wire are constant,
  voltage : ∃ v : f.center → ℝ, (∀ x, v (f.fwd x) = (a x).1) ∧ (∀ x, v (f.bwd x) = (b x).1)
  -- and the current into any set of wires matches the current out.
  current (S : Set f.center) : ∑ x with f.fwd x ∈ S, (a x).2 = ∑ x with f.bwd x ∈ S, (b x).2

theorem Kirchhoff.congr (e : 𝔽.Cospan.Equiv f g) : Kirchhoff f a b ↔ Kirchhoff g a b := by
  suffices ∀ f g, 𝔽.Cospan.Equiv f g → Kirchhoff f a b → Kirchhoff g a b by constructor; apply this f g e; apply this g f e.symm
  clear f g e; intro f g e H
  constructor
  · obtain ⟨v,H1,H2⟩ := H.voltage
    exists v ∘ e.center.symm; constructor
    · simp [<-H1, <-e.fwd]
    · simp [<-H2, <-e.bwd]
  · intro S
    calc  ∑ x with g.fwd x ∈ S, (a x).2
      _ = ∑ x with f.fwd x ∈ e.center ⁻¹' S, (a x).2 := ?_
      _ = ∑ x with f.bwd x ∈ e.center ⁻¹' S, (b x).2 := H.current _
      _ = ∑ x with g.bwd x ∈ S, (b x).2 := ?_
    all_goals (congr; funext x; simp only [Set.mem_preimage]; congr; simp [<-e.fwd, <-e.bwd])



theorem Kirchhoff.equiv {α β : 𝔽} (f : α ≃ β) (a : β → ℝ × ℝ) : Kirchhoff (𝔽.Cospan.ofEquiv f) (a ∘ f) a where
  voltage := ⟨fun x => (a x).1, fun _ => rfl, fun _ => rfl⟩
  current S := by
    apply Finset.sum_equiv f
    · intro i; simp [𝔽.Cospan.ofEquiv, 𝔽.Cospan.ofFwd]
    · intro _ _; rfl

theorem Kirchhoff.id : Kirchhoff 𝔽.Cospan.id a a := Kirchhoff.equiv (Equiv.refl _) a

theorem Kirchhoff.comp (H1 : Kirchhoff f a b) (H2 : Kirchhoff g b c) : Kirchhoff (f.comp g) a c where
  voltage := by
    obtain ⟨⟨v1, _, _⟩, _⟩ := H1
    obtain ⟨⟨v2, _, _⟩, _⟩ := H2
    exists Pushout.lift v1 v2 $ by simp [*]
  current S := by
    calc  ∑ x with f.fwd x ∈ Pushout.inl ⁻¹' S, (a x).2
      _ = ∑ x with f.bwd x ∈ Pushout.inl ⁻¹' S, (b x).2 := H1.current _
      _ = ∑ x with g.fwd x ∈ Pushout.inr ⁻¹' S, (b x).2 := by congr; funext x; simp only [Set.mem_preimage]; congr; apply Pushout.sound
      _ = ∑ x with g.bwd x ∈ Pushout.inr ⁻¹' S, (c x).2 := H2.current _

theorem Kirchhoff.merge (ι : 𝔽) {α β : ι → 𝔽} (f : ∀ i, 𝔽.Cospan (α i) (β i)) {a : ∀ i, (α i) → ℝ × ℝ} {b : ∀ i, (β i) → ℝ × ℝ}
  (H : ∀ i, Kirchhoff (f i) (a i) (b i)) :
  Kirchhoff (𝔽.Cospan.merge f) (fun ⟨i,x⟩ => a i x) (fun ⟨i,x⟩ => b i x)
where
  voltage := by
    obtain ⟨v,H⟩ := Classical.axiomOfChoice fun i => (H i).voltage
    exists fun ⟨i,x⟩ => v i x
    constructor
    · intro ⟨i,x⟩; simp [<-(H i).1 x]; rfl
    · intro ⟨i,x⟩; simp [<-(H i).2 x]; rfl
  current S := by
    trans (∑ i, ∑ x with (𝔽.Cospan.merge f).bwd ⟨i, x⟩ ∈ S, (b i x).2)
    trans (∑ i, ∑ x with (𝔽.Cospan.merge f).fwd ⟨i, x⟩ ∈ S, (a i x).2)

    rotate_left
    congr; funext i; exact ((H i).current {x | ⟨i,x⟩ ∈ S})
    rotate_right

    all_goals simp only [Finset.sum_sigma']; congr; ext ⟨i,x⟩; simp

theorem Kirchhoff.equiv_implies f : Kirchhoff (𝔽.Cospan.ofEquiv f) a b → a = b ∘ f := by
  intro ⟨⟨v, H1, H2⟩, H3⟩
  ext wire <;> unfold Function.comp
  · rw [<- H1 wire, <- H2 (f wire)]; rfl
  · calc  (a wire).2
      _ = ∑ x ∈ {wire}, (a x).2 := by rw [Finset.sum_singleton]
      _ = ∑ x with (𝔽.Cospan.ofEquiv f).fwd x ∈ Set.singleton (f wire), (a x).2 := ?_
      _ = ∑ x with (𝔽.Cospan.ofEquiv f).bwd x ∈ Set.singleton (f wire), (b x).2 := H3 _
      _ = ∑ x ∈ {f wire}, (b x).2 := ?_
      _ = (b (f wire)).2 := by rw [Finset.sum_singleton]
    all_goals congr; ext y; simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and]
    · change y = wire ↔ f y ∈ {f wire}; simp [Set.mem_singleton_iff]
    · exact Set.mem_singleton_iff
theorem Kirchhoff.id_implies : Kirchhoff 𝔽.Cospan.id a b → a = b := Kirchhoff.equiv_implies (Equiv.refl _)

theorem Kirchhoff.merge_implies (ι : 𝔽) {α β : ι → 𝔽} (f : ∀ i, 𝔽.Cospan (α i) (β i)) {a : (i : ι) × (α i) → ℝ × ℝ} {b : (i : ι) × (β i) → ℝ × ℝ} :
  Kirchhoff (𝔽.Cospan.merge f) a b → ∀ i, Kirchhoff (f i) (fun x => a ⟨i,x⟩) (fun x => b ⟨i,x⟩)
:= by
  intro H i; constructor
  · obtain ⟨v,H1,H2⟩ := H.voltage
    exists (fun x => v ⟨i,x⟩)
    constructor <;> intro x
    · exact H1 ⟨i,x⟩
    · exact H2 ⟨i,x⟩
  · intro S

    calc  ∑ x with (f i).fwd x ∈ S, (a ⟨i, x⟩).2
      _ = ∑ j, ∑ x with (𝔽.Cospan.merge f).fwd ⟨j,x⟩ ∈ Sigma.mk i '' S, (a ⟨j,x⟩).2 := ?_
      _ = ∑ x with (𝔽.Cospan.merge f).fwd x ∈ Sigma.mk i '' S, (a x).2              := ?_
      _ = ∑ x with (𝔽.Cospan.merge f).bwd x ∈ Sigma.mk i '' S, (b x).2              := ?_
      _ = ∑ j, ∑ x with (𝔽.Cospan.merge f).bwd ⟨j,x⟩ ∈ Sigma.mk i '' S, (b ⟨j,x⟩).2 := ?_
      _ = ∑ x with (f i).bwd x ∈ S, (b ⟨i, x⟩).2                                    := ?_

    · rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
      · congr; ext x; simp [𝔽.Cospan.merge, Sigma.map]
      · intro j _ neq; rw [ne_eq, <-iff_false, Eq.comm] at neq; simp [𝔽.Cospan.merge, Sigma.map, neq]
    · simp only [Finset.sum_sigma']; apply Finset.sum_congr; ext; simp only [Set.mem_image, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]; intro ⟨i,x⟩ _; rfl
    · exact H.current (Sigma.mk i '' S)
    · simp only [Finset.sum_sigma']; apply Finset.sum_congr; ext; simp only [Set.mem_image, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]; intro ⟨i,x⟩ _; rfl
    · rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
      · congr; ext x; simp [𝔽.Cospan.merge, Sigma.map]
      · intro j _ neq; rw [ne_eq, <-iff_false, Eq.comm] at neq; simp [𝔽.Cospan.merge, Sigma.map, neq]


theorem Kirchhoff.equiv_iff f : Kirchhoff (𝔽.Cospan.ofEquiv f) a b ↔ a = b ∘ f := by
  constructor
  · exact Kirchhoff.equiv_implies f
  · intro e; cases e; exact Kirchhoff.equiv f b
theorem Kirchhoff.id_iff : Kirchhoff 𝔽.Cospan.id a b ↔ a = b := Kirchhoff.equiv_iff (Equiv.refl _)

theorem Kirchhoff.merge_iff (ι : 𝔽) {α β : ι → 𝔽} (f : ∀ i, 𝔽.Cospan (α i) (β i)) {a : (i : ι) × (α i) → ℝ × ℝ} {b : (i : ι) × (β i) → ℝ × ℝ} :
  Kirchhoff (𝔽.Cospan.merge f) a b ↔ ∀ i, Kirchhoff (f i) (fun x => a ⟨i,x⟩) (fun x => b ⟨i,x⟩)
:= by
  constructor
  · exact Kirchhoff.merge_implies ι f
  · intro H; apply Kirchhoff.merge ι f H


--------------------------------------------------------------------------------
-- `Kirchhoff.comp_implies` is significantly harder
-- than the rest of the theorems in this file.
-- This section proves a whole buch of lemmas needed to prove it.

private structure Wiring where
  Terminal : 𝔽
  Wire : 𝔽
  src : Wire → Terminal
  tgt : Wire → Terminal
private def Wiring.Component (W : Wiring) : Type := Coequalizer W.src W.tgt
private def Wiring.component (W : Wiring) : W.Terminal → W.Component := Coequalizer.inj
private def Wiring.Supports (W : Wiring) (c : W.Terminal → ℝ) : Prop :=
  ∃ c' : W.Wire → ℝ, ∀ S : Set W.Terminal,
    ∑ w with W.src w ∈ S, c' w =
    ∑ w with W.tgt w ∈ S, c' w + ∑ x ∈ S, c x

private lemma Wiring.Supports.wire (w : Wiring.Wire W) :
  W.Supports (fun x => (if x = W.src w then k else 0) - (if x = W.tgt w then k else 0))
:= by
  exists fun x => if x = w then k else 0
  intro S; simp

private lemma Wiring.Supports.connected (a b : Wiring.Terminal W)
  (H : W.component a = W.component b) :
  W.Supports (fun x => (if x = a then k else 0) - (if x = b then k else 0))
:= by
  unfold Wiring.component Coequalizer.inj at H
  rw [Quot.eq] at H
  induction H with
  | rel a b H =>
    obtain ⟨w,H1,H2⟩ := H; rw [H1, H2]
    apply Wiring.Supports.wire
  | refl => exists fun _ => 0; intro S; simp
  | symm a b _ IH =>
    obtain ⟨c,H⟩ := IH; exists -c
    intro S; specialize H S
    simp only [Pi.neg_apply, Finset.sum_neg_distrib]
    rw [H]; simp; linarith
  | trans a b _ _ _ IH1 IH2 =>
    obtain ⟨c1,H1⟩ := IH1; obtain ⟨c2,H2⟩ := IH2; exists c1 + c2
    intro S; specialize H1 S; specialize H2 S
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [H1, H2]; simp; linarith

private lemma Wiring.Supports.sum (ι : 𝔽) (c : ι → Wiring.Terminal W → ℝ)
  (H : ∀ i, W.Supports (c i)) : W.Supports (fun x => ∑ i, c i x)
:= by
  obtain ⟨c',H⟩ := axiomOfChoice H
  exists fun x => ∑ i, c' i x
  intro S
  calc  ∑ w with W.src w ∈ S, ∑ i, c' i w
    _ = ∑ i, ∑ w with W.src w ∈ S, c' i w := by rw [Finset.sum_comm]
    _ = ∑ i, (∑ w with W.tgt w ∈ S, c' i w + ∑ x ∈ S, c i x) := by congr; funext; apply H
    _ = ∑ i, ∑ w with W.tgt w ∈ S, c' i w + ∑ i, ∑ x ∈ S, c i x := by apply Finset.sum_add_distrib
    _ = ∑ w with W.tgt w ∈ S, ∑ i, c' i w + ∑ x ∈ S, ∑ i, c i x := by apply congrArg₂ <;> rw [Finset.sum_comm]

private lemma Wiring.Supports.component (W : Wiring) (c : W.Terminal → ℝ) :
  (∀ S : Set W.Component, ∑ x with W.component x ∈ S, c x = 0) → W.Supports c
:= by
  let surj : W.component.Surjective := by apply Coequalizer.ind; intro x; exists x
  obtain ⟨choice,right_inv⟩ := surj.hasRightInverse

  intro H
  suffices c = fun x => ∑ w, ((if x = w then (c w) else 0) - if x = choice (W.component w) then (c w) else 0) by {
    rw [this]
    apply Wiring.Supports.sum; intro w
    apply Wiring.Supports.connected
    exact (right_inv _).symm
  }

  funext x
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  suffices (∑ w, if x = choice (W.component w) then c w else 0) = 0 by linarith
  rw [<-Finset.sum_filter]
  exact H {w | x = choice w}

private lemma pushout_currents {α β γ : 𝔽} (f : β → α) (g : β → γ) (c1 : α → ℝ) (c2 : γ → ℝ)
  (H : ∀ S : Set (Pushout f g),
    ∑ x with Pushout.inl x ∈ S, c1 x =
    ∑ x with Pushout.inr x ∈ S, c2 x) :
  ∃ c : β → ℝ,
    (∀ S : Set _, ∑ x with f x ∈ S, c x = ∑ x ∈ S, c1 x) ∧
    (∀ S : Set _, ∑ x with g x ∈ S, c x = ∑ x ∈ S, c2 x)
:= by
  let W := Wiring.mk (α ⊕ γ) β (Sum.inl ∘ f) (Sum.inr ∘ g)
  obtain ⟨c,H⟩ := Wiring.Supports.component W (Sum.elim c1 (Neg.neg ∘ c2)) $ by
    intro S
    calc  ∑ x with W.component x ∈ S, Sum.elim c1 (Neg.neg ∘ c2) x
      _ = ∑ x with W.component (Sum.inl x) ∈ S, c1 x
        + ∑ x with W.component (Sum.inr x) ∈ S, -c2 x := by
          rw [<-Finset.sum_sum_elim]
          congr
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_disjSum]
          cases x <;> simp
      _ = ∑ x with Pushout.inl x ∈ S, c1 x
        + ∑ x with Pushout.inr x ∈ S, -c2 x := rfl
      _ = ∑ x with Pushout.inr x ∈ S, c2 x
        + ∑ x with Pushout.inr x ∈ S, -c2 x := by rw [H]
      _ = ∑ x with Pushout.inr x ∈ S, (c2 x + -c2 x) := by rw [Finset.sum_add_distrib]
      _ = ∑ x with Pushout.inr x ∈ S, 0 := by congr; funext; linarith
      _ = 0 := by apply Finset.sum_eq_zero; intro _ _; rfl

  have H1 : ∀ (S : Set α), ∑ w with f w ∈ S, c w = ∑ x ∈ S, c1 x := by
    intro S
    have:= H (Sum.inl '' S)
    simp only [Function.comp_apply, Set.mem_image, Sum.inl.injEq, exists_eq_right, and_false,
      exists_false, Finset.filter_False, Finset.sum_empty, Set.toFinset_image, Set.mem_toFinset,
      imp_self, implies_true, Finset.sum_image, Sum.elim_inl, zero_add] at this
    exact this
  have H2 : ∀ (S : Set γ), ∑ w with g w ∈ S, c w = ∑ x ∈ S, c2 x := by
    intro S
    have:= H (Sum.inr '' S)
    simp only [Function.comp_apply, Set.mem_image, and_false, exists_false, Finset.filter_False,
      Finset.sum_empty, Sum.inr.injEq, exists_eq_right, Set.toFinset_image, Set.mem_toFinset,
      imp_self, implies_true, Finset.sum_image, Sum.elim_inr, Finset.sum_neg_distrib] at this
    linarith
  exists c

--------------------------------------------------------------------------------

theorem Kirchhoff.comp_implies {f : 𝔽.Cospan α β} {g : 𝔽.Cospan β γ} : Kirchhoff (𝔽.Cospan.comp f g) a c → ∃ b, Kirchhoff f a b ∧ Kirchhoff g b c := by
  intro ⟨⟨v, H1, H2⟩, H3⟩

  obtain ⟨internalCurrent,H4,H5⟩ := pushout_currents f.bwd g.fwd
    (fun x => ∑ y with f.fwd y = x, (a y).2)
    (fun x => ∑ y with g.bwd y = x, (c y).2)
    fun S => by
      rw [Finset.sum_fiberwise_eq_sum_filter Finset.univ (Finset.filter (fun x => Pushout.inl x ∈ S) Finset.univ)]
      rw [Finset.sum_fiberwise_eq_sum_filter Finset.univ (Finset.filter (fun x => Pushout.inr x ∈ S) Finset.univ)]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact H3 S

  exists fun x => (v (Pushout.inl (f.bwd x)), internalCurrent x)
  constructor
  · constructor
    · exists (v ∘ Pushout.inl)
      constructor
      · exact H1
      · intro _; rfl
    · intro S; simp only; rw [H4 S]
      rw [Finset.sum_fiberwise_eq_sum_filter Finset.univ S.toFinset]
      congr; funext; rw [Set.mem_toFinset]
  · constructor
    · exists (v ∘ Pushout.inr)
      constructor
      · intro _; simp only [Function.comp_apply]; rw [Pushout.sound]
      · exact H2
    · intro S; simp only; rw [H5 S]
      rw [Finset.sum_fiberwise_eq_sum_filter Finset.univ S.toFinset]
      congr; funext; rw [Set.mem_toFinset]

theorem Kirchhoff.comp_iff : Kirchhoff (𝔽.Cospan.comp f g) a c ↔ ∃ b, Kirchhoff f a b ∧ Kirchhoff g b c := by
  constructor
  · exact Kirchhoff.comp_implies
  · intro ⟨b,H1,H2⟩; apply Kirchhoff.comp H1 H2
