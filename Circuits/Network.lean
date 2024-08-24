import «Circuits».Utils

structure Network (Component : Type) (Terminal : Component → 𝔽) (α : 𝔽) where
  Node : 𝔽
  component : Node → Component
  wiring : 𝔽.Cospan ((n : Node) × Terminal (component n)) α

def Network.single (c : Component) : Network Component Terminal (Terminal c) where
  Node := Unit
  component := fun () => c
  wiring := 𝔽.Cospan.ofFwd (fun ⟨(),x⟩ => x)

def Network.map (f : 𝔽.Cospan α β) (net : Network Component Terminal α) : Network Component Terminal β where
  Node := net.Node
  component := net.component
  wiring := net.wiring.comp f

def Network.merge (ι : 𝔽) (α : ι → 𝔽) (nets : (i : ι) → Network Component Terminal (α i)) : Network Component Terminal ⟨(i : ι) × α i⟩ where
  Node := (i : ι) × (nets i).Node
  component := fun ⟨i,n⟩ => (nets i).component n
  wiring := 𝔽.Cospan.comp
    (𝔽.Cospan.ofFwd $ by
      simp only
      exact (Equiv.sigmaAssoc (fun i n => Terminal ((nets i).component n))).toFun)
    (𝔽.Cospan.merge (fun i => (nets i).wiring))
