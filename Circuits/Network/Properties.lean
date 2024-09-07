import Mathlib.Data.FinEnum
import «Circuits».Network.Concrete
import «Circuits».Network.Abstract

namespace Network

structure Represents
  {Component : Type} [Inhabited Component]
  {Terminal : Component → Type} [∀ c, FinEnum (Terminal c)]
  {α : Type} [FinEnum α]
  (conc : Concrete Component)
  (abs : Abstract Component (fun c => Terminal c) α)
where
  node : abs.Node → ℕ
  component (n : abs.Node) : abs.component n = (conc.nodes.get! (node n)).1
  wiring_center : abs.wiring.center → ℕ
  wiring_bwd (a : α) : wiring_center (abs.wiring.bwd a) = conc.terminals.get! (FinEnum.equiv a)
  wiring_fwd (n : abs.Node) (t : Terminal (abs.component n)) :
    wiring_center (abs.wiring.fwd ⟨n,t⟩) = (conc.nodes.get! (node n)).2.get! (FinEnum.equiv t)

structure Bundled
  (Component : Type) [Inhabited Component]
  (Terminal : Component → Type) [∀ c, FinEnum (Terminal c)]
  (α : Type) [FinEnum α]
where
  concrete : Concrete Component
  abstract : Abstract Component (fun c => Terminal c) α
  repr : Represents concrete abstract

lemma Array.getD_eq_getElem {α : Type u} (l : Array α) (d : α) {n : ℕ} (hn : n < l.size) : l.getD n d = l[n] := by
  simp only [Array.getD, Array.get_eq_getElem]; split <;> rfl

def Bundled.single
  {Component : Type} [Inhabited Component]
  {Terminal : Component → Type} [∀ c, FinEnum (Terminal c)]
  (c : Component) :
  Bundled Component Terminal (Terminal c)
where
  concrete := Concrete.single c (FinEnum.card (Terminal c))
  abstract := Abstract.single c
  repr.node := fun () => 0
  repr.component := fun () => rfl
  repr.wiring_center := by
    change Terminal c → ℕ
    exact fun x => ↑(FinEnum.equiv x)
  repr.wiring_fwd := fun () x => by
    change (FinEnum.equiv x).val = (Array.ofFn fun i => ↑i).get! (FinEnum.equiv x).val
    rw [Array.get!, Array.getD_eq_getElem, Array.getElem_ofFn]
    simp only [Array.size_ofFn]
    apply Fin.isLt
  repr.wiring_bwd x := by
    change (FinEnum.equiv x).val = (Array.ofFn fun i => ↑i).get! (FinEnum.equiv x).val
    rw [Array.get!, Array.getD_eq_getElem, Array.getElem_ofFn]
    simp only [Array.size_ofFn]
    apply Fin.isLt
