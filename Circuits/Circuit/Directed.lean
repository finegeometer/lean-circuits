import «Circuits».Circuit

namespace Circuit

-- A circuit with a notion of "input" and "output".
def Directed (α β : 𝔽) := Circuit (α ⊕ β)

-- Compose a large number of circuits in series.
def Directed.series n (α : Fin n.succ → 𝔽)
  (c : (i : Fin n) → Directed (α i.castSucc) (α i.succ)) :
  Directed (α 0) (α (Fin.last n))
:= (merge (Fin n) c).map
  ⟨ (i : Fin n.succ) × α i
  , by
    intro ⟨i,x⟩
    cases x with | inl x => exact ⟨i.castSucc,x⟩ | inr x => exact ⟨i.succ,x⟩
  , Sum.elim (fun x => ⟨0,x⟩) (fun x => ⟨Fin.last n,x⟩)
  ⟩

def Directed.parallel (ι : 𝔽) {α β : ι → 𝔽}
  (c : (i : ι) → Directed (α i) (β i)) :
  Directed ((i : ι) × α i) ((i : ι) × β i)
:= (merge ι c).map (𝔽.Cospan.ofEquiv (by exact Equiv.sigmaSumDistrib (fun i => α i) (fun i => β i)))

def Directed.reverse (c : Directed α β) : Directed β α :=
  c.map (𝔽.Cospan.ofEquiv (by exact Equiv.sumComm α β))

def Directed.wire (f : 𝔽.Cospan α β) : Directed α β :=
  (@merge Empty Empty.elim Empty.rec).map
    ⟨ f.center
    , Empty.elim ∘ Sigma.fst
    , Sum.elim f.fwd f.bwd
    ⟩

--------------------------------------------------------------------------------

instance {α β : 𝔽} : Membership ((α → ℝ → ℝ × ℝ) × (β → ℝ → ℝ × ℝ)) (Directed α β) where
  mem := by
    unfold Directed
    intro ⟨inputs, outputs⟩ circ
    exact Sum.elim inputs (fun x t => ((outputs x t).1, -(outputs x t).2)) ∈ circ

@[ext]
theorem Directed.ext (c1 c2 : Directed α β) :
  (∀ input output, (input, output) ∈ c1 ↔ (input, output) ∈ c2) → c1 = c2
:= by
  intro H
  unfold Directed Circuit; ext bhvr
  specialize H (bhvr ∘ Sum.inl) (fun x t => let (V,I) := bhvr (Sum.inr x) t; (V,-I))
  unfold Circuit.instMembershipProdForallTForallRealDirected at H; simp at H
  rw [<-Sum.elim_comp_inl_inr bhvr]; exact H

def Directed.ofPred {α β : 𝔽} (P : (α → ℝ → ℝ × ℝ) → (β → ℝ → ℝ × ℝ) → Prop) : Directed α β := by
    unfold Directed
    exact {bhvr | P (fun x t => bhvr (Sum.inl x) t) (fun x t => let (V,I) := bhvr (Sum.inr x) t; (V,-I))}

@[simp]
theorem Directed.mem_ofPred :
  x ∈ Directed.ofPred P ↔ P x.1 x.2
:= by
  unfold ofPred Circuit.instMembershipProdForallTForallRealDirected
  simp; rw [Set.mem_setOf]; simp

instance : CompleteLattice (Directed α β) := by
  unfold Directed
  exact inferInstance

theorem Directed.le_def {c1 c2 : Directed α β} :
  c1 ≤ c2 ↔ ∀ input output, (input, output) ∈ c1 → (input, output) ∈ c2
:= by
  trans; exact Circuit.le_def
  constructor
  · intro H input output
    exact H (Sum.elim input (fun x t => let (V,I) := output x t; (V,-I)))
  · intro H bhvr
    specialize H (fun x t => bhvr (Sum.inl x) t) (fun x t => let (V,I) := bhvr (Sum.inr x) t; (V,-I))
    unfold Circuit.instMembershipProdForallTForallRealDirected at H; simp at H
    change (Sum.elim (bhvr ∘ Sum.inl) (bhvr ∘ Sum.inr)) ∈ _ →
           (Sum.elim (bhvr ∘ Sum.inl) (bhvr ∘ Sum.inr)) ∈ _ at H
    simp at H; exact H

------------------------------------------------------------------------------

theorem Directed.mem_reverse (c : Directed α β) :
  (input, output) ∈ Directed.reverse c ↔
  ( fun x t => let (V,I) := output x t; (V,-I)
  , fun x t => let (V,I) := input x t; (V,-I)
  ) ∈ c
:= by
  rw [reverse, Circuit.map_ofEquiv, id_eq]
  unfold Directed Circuit.instMembershipProdForallTForallRealDirected
  simp only [Set.preimage, id_eq, neg_neg]; rw [Set.mem_setOf, iff_eq_eq]
  congr; funext x; cases x <;> rfl

theorem Directed.mem_parallel {ι : 𝔽} {α β : ι → 𝔽} (c : (i : ι) → Directed (α i) (β i))
  (input : (i : ι) × α i → ℝ → ℝ × ℝ) (output : (i : ι) × β i → ℝ → ℝ × ℝ) :
  (input, output) ∈ parallel ι c ↔
  ∀ i : ι, (fun x => input ⟨i,x⟩, fun x => output ⟨i,x⟩) ∈ c i
:= by
  unfold Directed Circuit.instMembershipProdForallTForallRealDirected
  simp only [parallel, Circuit.map_ofEquiv, id_eq]
  rw [Set.mem_preimage, merge]
  simp only [Set.mem_setOf_eq, Function.comp_apply, Equiv.sigmaSumDistrib_apply, Sum.elim_map]
  rfl


open Classical
noncomputable local instance (α : Type) [Finite α] : Fintype α := Fintype.ofFinite α


theorem Directed.mem_wire (f : 𝔽.Cospan α β) :
  (input, output) ∈ Directed.wire f ↔ ∀ t, Kirchhoff f (fun x => input x t) (fun x => output x t)
:= by
  constructor
  · intro ⟨bhvr,_,H⟩ t
    constructor
    · obtain ⟨v, _, H⟩ := (H t).1
      exists v; constructor
      · exact fun x => H (Sum.inl x)
      · exact fun x => H (Sum.inr x)
    · intro S
      have:= calc 0
        _ = ∑ x ∈ _, (bhvr x t).2 := by simp
        _ = _ := (H t).2 S
        _ = ∑ x ∈ Finset.disjSum
          (Finset.filter (fun x => f.fwd x ∈ S) Finset.univ)
          (Finset.filter (fun x => f.bwd x ∈ S) Finset.univ),
          (Sum.elim (fun x => (input x t).2) (fun x => -(output x t).2) x )
        := by
          congr
          · ext x; cases x <;> simp [Finset.mem_disjSum]
          · funext x; cases x <;> simp
        _ = ∑ x with f.fwd x ∈ S, (input x t).2 + - ∑ x with f.bwd x ∈ S, (output x t).2
        := by simp
      linarith [this]
  · intro H
    exists Empty.elim ∘ Sigma.fst
    constructor; exact fun i : Empty => i.elim
    intro t
    constructor
    · obtain ⟨v, H1, H2⟩ := (H t).1
      exists v; constructor; exact fun ⟨i,_⟩ => i.elim
      intro x; cases x <;> simp [H1, H2]
    · intro S
      calc _
        _ = (0 : ℝ) := by simp
        _ = ∑ x ∈ Finset.disjSum
          (Finset.filter (fun x => f.fwd x ∈ S) Finset.univ)
          (Finset.filter (fun x => f.bwd x ∈ S) Finset.univ),
          (Sum.elim (fun x => (input x t).2) (fun x => -(output x t).2) x ) := by simp [(H t).2]
        _ = _ := by
          congr
          · ext x; cases x <;> simp [Finset.mem_disjSum]
          · funext x; cases x <;> simp



private lemma telescope {n : ℕ} (f : Fin n.succ → ℝ) :
  ∑ i : Fin n, (f i.castSucc - f i.succ) = f 0 - f (Fin.last n)
:= calc
  ∑ i : Fin n, (f i.castSucc - f i.succ)
  _ = ∑ i : Fin n, f i.castSucc - ∑ i : Fin n, f i.succ                          := by rw [Finset.sum_sub_distrib]
  _ = ∑ i ∈ Finset.map ⟨Fin.castSucc, Fin.castSucc_injective n⟩ Finset.univ, f i
    - ∑ i ∈ Finset.map ⟨Fin.succ, Fin.succ_injective n⟩ Finset.univ, f i         := by rw [Finset.sum_map, Finset.sum_map]; rfl
  _ = ∑ i ∈ Finset.univ.erase (Fin.last n), f i - ∑ i ∈ Finset.univ.erase 0, f i := by congr <;> (ext i; simp [Fin.exists_castSucc_eq, Fin.exists_succ_eq])
  _ = (∑ i, f i - f (Fin.last n)) - (∑ i, f i - f 0)                             := by simp [Finset.sum_erase_eq_sub]
  _ = f 0 - f (Fin.last n)                                                       := by linarith


theorem Directed.mem_series {n : ℕ} (α : Fin n.succ → 𝔽) (c : (i : Fin n) → Directed (α i.castSucc) (α i.succ))
  (input : α 0 → ℝ → ℝ × ℝ) (output : α (Fin.last n) → ℝ → ℝ × ℝ) :
  (input, output) ∈ Directed.series n α c ↔
  ∃ bhvr : (i : Fin n.succ) → α i → ℝ → ℝ × ℝ,
  (∀ i : Fin n, (bhvr i.castSucc, bhvr i.succ) ∈ c i) ∧
  input = bhvr 0 ∧ output = bhvr (Fin.last n)
:= by
  constructor
  · intro ⟨bhvr,pf,H⟩

    -- Plan: I need to produce a function. I'll define it *twice*, and prove the two versions equal.
    let bhvr₁ : (i : Fin n.succ) → α i → ℝ → ℝ × ℝ :=
      Fin.cases input (fun i x t => let (V,I) := bhvr ⟨i,Sum.inr x⟩ t; (V,-I))
    let bhvr₂ : (i : Fin n.succ) → α i → ℝ → ℝ × ℝ :=
      Fin.lastCases output (fun i x t => bhvr ⟨i,Sum.inl x⟩ t)

    have bhvr_eq : bhvr₁ = bhvr₂ := by
      ext i x t
      · obtain ⟨v, H⟩ := axiomOfChoice fun t => (H t).voltage
        simp only at v H
        obtain ⟨H1,H2⟩ := H t; clear H; clear H
        calc (bhvr₁ i x t).1
          _ = v t ⟨i,x⟩ := ?_
          _ = (bhvr₂ i x t).1 := ?_
        · revert i; apply Fin.cases
          · simp only [bhvr₁, Fin.cases_zero]
            intro x; exact (H2 (Sum.inl x)).symm
          · simp only [bhvr₁, Fin.cases_succ]
            intro i x; exact (H1 ⟨i, Sum.inr x⟩).symm
        · revert i; apply Fin.lastCases
          · simp only [bhvr₂, Fin.lastCases_last]
            intro x; exact H2 (Sum.inr x)
          · simp only [bhvr₂, Fin.lastCases_castSucc]
            intro i x; exact H1 ⟨i, Sum.inl x⟩
      · suffices (bhvr₁ i x t).2 - (bhvr₂ i x t).2 = 0 by linarith

        let S : Set ((i : Fin n.succ) × α i) := {⟨i,x⟩}
        suffices ∑ x ∈ S, (bhvr₁ x.fst x.snd t).2 - ∑ x ∈ S, (bhvr₂ x.fst x.snd t).2 = 0 by
          simp [S, Finset.sum_singleton] at this; exact this

        let S' i := {x | ⟨i,x⟩ ∈ S}
        have: S.toFinset = Finset.univ.sigma (fun i => (S' i).toFinset) := by
          ext ⟨i,x⟩; simp [S']
        rw [this, Finset.sum_sigma, Finset.sum_sigma]; clear this

        have:= calc ∑ i : Fin n.succ, ∑ x ∈ (S' i).toFinset, (bhvr₁ i x t).2
          _ = ∑ x ∈ (S' 0).toFinset, (bhvr₁ 0 x t).2 + ∑ i ∈ Finset.univ.erase 0, ∑ x ∈ (S' i).toFinset, (bhvr₁ i x t).2 := by simp [Finset.add_sum_erase]
          _ = ∑ x ∈ (S' 0).toFinset, (bhvr₁ 0 x t).2 + ∑ i ∈ Finset.univ.map ⟨Fin.succ,Fin.succ_injective n⟩, ∑ x ∈ (S' i).toFinset, (bhvr₁ i x t).2 := by congr; ext i; revert i; apply Fin.cases <;> simp [Fin.succ_ne_zero]
          _ = ∑ x ∈ (S' 0).toFinset, (bhvr₁ 0 x t).2 + ∑ i : Fin n, ∑ x ∈ (S' i.succ).toFinset, (bhvr₁ i.succ x t).2 := by rw [Finset.sum_map]; rfl
        rw [this]; clear this

        have:= calc ∑ i : Fin n.succ, ∑ x ∈ (S' i).toFinset, (bhvr₂ i x t).2
          _ = ∑ x ∈ (S' (Fin.last n)).toFinset, (bhvr₂ (Fin.last n) x t).2 + ∑ i ∈ Finset.univ.erase (Fin.last n), ∑ x ∈ (S' i).toFinset, (bhvr₂ i x t).2 := by simp [Finset.add_sum_erase]
          _ = ∑ x ∈ (S' (Fin.last n)).toFinset, (bhvr₂ (Fin.last n) x t).2 + ∑ i ∈ Finset.univ.map ⟨Fin.castSucc,Fin.castSucc_injective n⟩, ∑ x ∈ (S' i).toFinset, (bhvr₂ i x t).2 := by
            congr; ext i; revert i; apply Fin.lastCases <;> simp [fun i => Fin.ne_of_lt (Fin.castSucc_lt_last i)]
          _ = ∑ x ∈ (S' (Fin.last n)).toFinset, (bhvr₂ (Fin.last n) x t).2 + ∑ i : Fin n, ∑ x ∈ (S' i.castSucc).toFinset, (bhvr₂ i.castSucc x t).2 := by rw [Finset.sum_map]; rfl
        rw [this]; clear this

        simp [Finset.sum_map, Finset.sum_map, bhvr₁, bhvr₂]

        have:= calc ∑ i : Fin n, (∑ x ∈ (S' i.castSucc).toFinset, (bhvr ⟨i,Sum.inl x⟩ t).2 + ∑ x ∈ (S' i.succ).toFinset, (bhvr ⟨i,Sum.inr x⟩ t).2)
          _ = ∑ x ∈ Finset.univ.sigma (fun i : Fin n => Finset.disjSum (S' i.castSucc).toFinset (S' i.succ).toFinset), (bhvr x t).2 := by rw [Finset.sum_sigma]; congr; funext; rw [Finset.sum_disj_sum]
          _ = _ := by congr; ext ⟨i,x⟩; cases x <;> simp only [Nat.succ_eq_add_one, Set.mem_setOf_eq, Set.toFinset_setOf, Finset.mem_sigma, Finset.mem_univ, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, Finset.mem_filter, true_and, S']
          _ = _ := (H t).current S
          _ = ∑ x ∈ Finset.disjSum (S' 0).toFinset (S' (Fin.last n)).toFinset, (Sum.elim input (fun x t => ((output x t).1, -(output x t).2)) x t).2 := by congr; ext x; cases x <;> simp only [Nat.succ_eq_add_one, Finset.mem_filter, Finset.mem_univ, Sum.elim_inl, Sum.elim_inr, true_and, Set.mem_setOf_eq, Set.toFinset_setOf, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, S']
          _ = ∑ x ∈ S' 0, (input x t).2 + ∑ x ∈ S' (Fin.last n), -(output x t).2 := by rw [Finset.sum_disj_sum]; simp
        simp [Finset.sum_add_distrib] at this
        linarith

    exists bhvr₁
    constructor
    · intro i
      nth_rewrite 1 [bhvr_eq]
      simp only [bhvr₁, bhvr₂, Fin.cases_succ, Fin.lastCases_castSucc]
      unfold Circuit.Directed
      calc _
        _ = _ := ?_
        _ ∈ _ := pf i
      ext x t <;> cases x <;> simp
    · constructor
      · simp only [bhvr₁, Fin.cases_zero]
      · simp only [bhvr_eq, bhvr₂, Fin.lastCases_last]


  · intro ⟨bhvr,H1,H2,H3⟩
    exists fun ⟨i,x⟩ t => match x with
      | Sum.inl x => bhvr i.castSucc x t
      | Sum.inr x => let (V,I) := bhvr i.succ x t; (V,-I)
    simp only
    constructor
    · intro i
      unfold Circuit.Directed at c
      calc _
        _ = _ := ?_
        _ ∈ c i := H1 i
      ext x t <;> cases x <;> simp
    · intro t
      rw [H2, H3]
      constructor
      · exists fun ⟨i,x⟩ => (bhvr i x t).1
        constructor
        · intro ⟨i,x⟩; cases x <;> rfl
        · intro x; cases x <;> rfl
      · simp only
        intro S
        let S' i := {x | ⟨i,x⟩ ∈ S}
        calc _
          _ = ∑ x ∈ Finset.univ.sigma (fun i : Fin n => Finset.disjSum (Set.toFinset (S' i.castSucc)) (Set.toFinset (S' i.succ))), Sum.elim (fun y => (bhvr x.1.castSucc y t).2) (fun y => -(bhvr x.1.succ y t).2) x.2 := by
            apply Finset.sum_congr
            · ext ⟨i,x⟩; cases x <;> simp only [Nat.succ_eq_add_one, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Set.toFinset_setOf, Finset.mem_sigma, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, S']
            · intro ⟨i,x⟩ _; cases x <;> rfl
          _ = ∑ i : Fin n, (∑ x ∈ Set.toFinset (S' i.castSucc), (bhvr i.castSucc x t).2 + ∑ x ∈ Set.toFinset (S' i.succ), -(bhvr i.succ x t).2) := by
            rw [Finset.sum_sigma]; congr; funext i
            rw [Finset.sum_disj_sum]; rfl
          _ = ∑ i : Fin n, (∑ x ∈ Set.toFinset (S' i.castSucc), (bhvr i.castSucc x t).2 - ∑ x ∈ Set.toFinset (S' i.succ), (bhvr i.succ x t).2) := by
            congr; funext; rw [Finset.sum_neg_distrib]; linarith
          _ = ∑ x ∈ (S' 0).toFinset, (bhvr 0 x t).2 - ∑ x ∈ (S' (Fin.last n)).toFinset, (bhvr (Fin.last n) x t).2 :=
            telescope (fun i => ∑ x ∈ Set.toFinset (S' i), (bhvr i x t).2)
          _ = ∑ x ∈ (S' 0).toFinset.disjSum (S' (Fin.last n)).toFinset, Sum.elim (fun x => (bhvr 0 x t).2) (fun x => -(bhvr (Fin.last n) x t).2) x := by
            rw [Finset.sum_disj_sum]; simp [Finset.sum_neg_distrib]; linarith
          _ = _ := by congr <;> ext x <;> cases x <;> simp [S']


--------------------------------------------------------------------------------

def Directed.id (α : 𝔽) : Directed α α :=
  Directed.series 0 (fun _ => α) Fin.elim0

def Directed.comp {α β γ : 𝔽} (c1 : Directed α β) (c2 : Directed β γ) : Directed α γ :=
  Directed.series 2
    (fun i => match i with | 0 => α | 1 => β | 2 => γ)
    (fun i => match i with | 0 => c1 | 1 => c2)



theorem Directed.mem_id {α : 𝔽} {input output : α → ℝ → ℝ × ℝ} :
  (input, output) ∈ Directed.id α ↔ input = output
:= by
  rw [Directed.id, Directed.mem_series (fun _ => α)]
  constructor
  · intro ⟨_,_,H1,H2⟩
    rw [H1,H2]; rfl
  · intro eq; cases eq
    exists fun _ => input
    constructor
    · apply Fin.rec0
    · constructor <;> rfl

theorem Directed.mem_comp {α β γ : 𝔽} {input : α → ℝ → ℝ × ℝ} {output : γ → ℝ → ℝ × ℝ}
  {c1 : Circuit.Directed α β} {c2 : Circuit.Directed β γ} :
  (input, output) ∈ Directed.comp c1 c2 ↔
  ∃ middle, (input, middle) ∈ c1 ∧ (middle, output) ∈ c2
:= by
  trans; apply Directed.mem_series
  constructor
  · intro ⟨bhvr,pf,H1,H2⟩
    exists bhvr 1
    constructor
    · rw [H1]; exact pf 0
    · rw [H2]; exact pf 1
  · intro ⟨middle,H1,H2⟩
    exists fun i => match i with | 0 => input | 1 => middle | 2 => output
    constructor
    · exact fun i => match i with | 0 => H1 | 1 => H2
    · constructor <;> rfl
