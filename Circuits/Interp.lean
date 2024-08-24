import «Circuits».Network
import «Circuits».Circuit

def Network.toCircuit (interp : (c : Component) → Circuit (Terminal c)) (net : Network Component Terminal α) : Circuit α :=
  Circuit.map net.wiring $
  Circuit.merge (ι := net.Node) (α := Terminal ∘ net.component) $
  fun node => interp (net.component node)



theorem Interp.single : (Network.single c).toCircuit interp = interp c := by
  simp only [Network.toCircuit, Network.single, Circuit.merge_unit, <-Circuit.comp_map, 𝔽.Cospan.ofEquiv]
  rw [Circuit.map.congr (g := 𝔽.Cospan.id), Circuit.id_map]
  exact (𝔽.Cospan.comp_ofFwd _ _).symm

theorem Interp.map (f : 𝔽.Cospan α β) (net : Network Component Terminal α) : (net.map f).toCircuit interp = (net.toCircuit interp).map f := by
  simp only [Network.toCircuit, Network.single, Network.map, <-Circuit.comp_map]

theorem Interp.merge {ι : 𝔽} {α : ι → 𝔽} (net : (i : ι) → Network Component Terminal (α i)) :
  (Network.merge ι α net).toCircuit interp = Circuit.merge ι (fun i => (net i).toCircuit interp)
:= by
  simp only [Network.toCircuit, Network.single, Circuit.merge_map]
  simp only [Network.merge, Circuit.merge_sigma, <-Circuit.comp_map]
  apply Circuit.map.congr
  calc 𝔽.Cospan.comp _ (𝔽.Cospan.comp _ (𝔽.Cospan.merge fun i => (net i).wiring))
    𝔽.Cospan.Equiv _ _ := (𝔽.Cospan.comp.assoc _ _ _).symm
    𝔽.Cospan.Equiv _ _ := 𝔽.Cospan.congr_comp _ _ _ ?_
    𝔽.Cospan.Equiv _ (𝔽.Cospan.merge fun i => (net i).wiring) := 𝔽.Cospan.comp.lunit _
  calc 𝔽.Cospan.comp _ _
    𝔽.Cospan.Equiv _ _ := (𝔽.Cospan.comp_ofFwd _ _).symm
    𝔽.Cospan.Equiv _ 𝔽.Cospan.id := ?_
  simp; apply 𝔽.Cospan.Equiv.refl
