import «Circuits».Kirchhoff

def Circuit (α : 𝔽) : Type := Set (α → ℝ → ℝ × ℝ)
instance {α : 𝔽} : Membership (α → ℝ → ℝ × ℝ) (Circuit α) := by unfold Circuit; exact inferInstance

open Classical
noncomputable local instance (α : Type) [Finite α] : Fintype α := Fintype.ofFinite α
def Circuit.map (f : 𝔽.Cospan α β) (circ : Circuit α) : Circuit β :=
  {bhvr | ∃ bhvr' ∈ circ, ∀ (t : ℝ), Kirchhoff f (fun x => bhvr' x t) (fun x => bhvr x t)}
def Circuit.merge (ι : 𝔽) {α : ι → 𝔽} (circ : (i : ι) → Circuit (α i)) : Circuit ⟨(i : ι) × α i⟩ :=
  {bhvr | ∀ i : ι, (fun x => bhvr ⟨i,x⟩) ∈ circ i}


--------------------------------------------------------------------------------
-- Theorems

theorem Circuit.map.congr {f g : 𝔽.Cospan α β} (e : f.Equiv g) (c : Circuit α) : c.map f = c.map g := by
  unfold map; simp [Kirchhoff.congr e]

theorem Circuit.map_ofEquiv {α β : 𝔽} (f : α ≃ β) (c : Circuit α) :
  c.map (𝔽.Cospan.ofEquiv f) = by unfold Circuit at *; exact (fun bhvr => bhvr ∘ f) ⁻¹' c
:= by
  unfold Circuit; ext bhvr
  simp [map, Kirchhoff.equiv_iff]
  constructor
  · intro ⟨bhvr',pf,H⟩
    suffices bhvr' = bhvr ∘ f by rw [<-this]; exact pf
    funext x t; exact congrFun (H t) x
  · intro pf; exists (fun x t => bhvr (f x) t), pf
    intro t; funext x; rfl
theorem Circuit.id_map (c : Circuit α) : c.map 𝔽.Cospan.id = c := Circuit.map_ofEquiv (Equiv.refl _) c

theorem Circuit.comp_map (f : 𝔽.Cospan α β) (g : 𝔽.Cospan β γ) (c : Circuit α) : c.map (f.comp g) = (c.map f).map g := by
  unfold Circuit; ext bhvr
  simp only [map, Kirchhoff.comp_iff, Set.mem_setOf_eq]
  constructor
  · intro ⟨bhvr'',pf,H⟩
    have ⟨bhvr',H⟩ := Classical.axiomOfChoice H
    exists fun x t => bhvr' t x
    constructor
    · exists bhvr'', pf
      intro t; specialize H t; exact H.1
    · intro t; specialize H t; exact H.2
  · intro ⟨bhvr', ⟨bhvr'', pf, H1⟩, H2⟩; exists bhvr'', pf
    intro t; specialize H1 t; specialize H2 t
    exists (fun x => bhvr' x t)

theorem Circuit.merge_unit (α : Unit → 𝔽) (cs : (i : Unit) → Circuit (α i)) :
  merge Unit cs = (cs ()).map (𝔽.Cospan.ofEquiv $ by exact (Equiv.unitSigma (fun i => α i)).symm)
:= by
  simp [Circuit.map_ofEquiv]
  unfold Circuit; ext bhvr
  simp only [merge, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · intro H; exact (H ())
  · intro H (); exact H

theorem Circuit.merge_sigma {ι : 𝔽} {κ : ι → 𝔽} (α : (i : ι) × κ i → 𝔽) (cs : (i : (i : ι) × κ i) → Circuit (α i)) :
  merge ((i : ι) × κ i) cs = (merge ι (fun i => merge (κ i) (fun k => cs ⟨i,k⟩))).map
    (𝔽.Cospan.ofEquiv $ by exact (Equiv.sigmaAssoc (fun i k => α ⟨i, k⟩)).symm)
:= by
  simp [Circuit.map_ofEquiv]
  unfold Circuit; ext bhvr
  constructor
  · intro H i k; exact H ⟨i,k⟩
  · intro H ⟨i,k⟩; exact H i k

theorem Circuit.merge_map (ι : 𝔽) (α β : ι → 𝔽) (f : (i : ι) → 𝔽.Cospan (α i) (β i)) (cs : (i : ι) → Circuit (α i)) :
  merge ι (fun i => (cs i).map (f i)) = (merge ι cs).map (𝔽.Cospan.merge f)
:= by
  unfold Circuit; ext bhvr
  simp [map, merge, Kirchhoff.merge_iff]
  constructor
  · intro H
    obtain ⟨bhvr',H⟩ := axiomOfChoice H
    exists fun ⟨i,x⟩ => bhvr' i x; constructor
    · intro i; exact (H i).1
    · intro t i; exact (H i).2 t
  · intro ⟨bhvr', pf, H⟩ i
    exists fun x => bhvr' ⟨i,x⟩, pf i
    intro t; exact H t i
