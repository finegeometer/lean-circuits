import «Circuits».Utils

namespace Network

structure Abstract (Component : Type) (Terminal : Component → 𝔽) (α : 𝔽) where
  Node : 𝔽
  component : Node → Component
  wiring : 𝔽.Cospan ((n : Node) × Terminal (component n)) α

def Abstract.single (c : Component) : Abstract Component Terminal (Terminal c) where
  Node := Unit
  component := fun () => c
  wiring := 𝔽.Cospan.ofFwd (fun ⟨(),x⟩ => x)

def Abstract.map (f : 𝔽.Cospan α β) (net : Abstract Component Terminal α) : Abstract Component Terminal β where
  Node := net.Node
  component := net.component
  wiring := net.wiring.comp f

def Abstract.merge (ι : 𝔽) (α : ι → 𝔽) (nets : (i : ι) → Abstract Component Terminal (α i)) : Abstract Component Terminal ⟨(i : ι) × α i⟩ where
  Node := (i : ι) × (nets i).Node
  component := fun ⟨i,n⟩ => (nets i).component n
  wiring := 𝔽.Cospan.comp
    (𝔽.Cospan.ofEquiv $ by exact (Equiv.sigmaAssoc (fun i n => Terminal ((nets i).component n))))
    (𝔽.Cospan.merge (fun i => (nets i).wiring))
