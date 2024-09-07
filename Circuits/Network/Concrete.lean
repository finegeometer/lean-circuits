import «Circuits».Utils

namespace Network

structure Concrete (Component : Type) where
  Wire : ℕ
  nodes : Array (Component × Array ℕ)
  terminals : Array ℕ
def Concrete.single (c : Component) (Terminal : ℕ) : Concrete Component where
  Wire := Terminal
  nodes := Array.mk [⟨c, Array.ofFn (n := Terminal) fun i => i⟩]
  terminals := Array.ofFn (n := Terminal) fun i => i
def Concrete.merge (nets : Array (Concrete Component)) : Concrete Component :=
  let offsets := Array.mk ((nets.toList.map Concrete.Wire).scanl Nat.add 0)
  let offset {k : ℕ} (i : Fin k) (n : ℕ) := offsets[i]! + n
  { Wire := offsets[nets.size]!
  , nodes := nets.concatMap fun net => net.nodes.map $ Prod.map id fun arr => arr.mapIdx offset
  , terminals := nets.concatMap fun net => net.terminals.mapIdx offset
  }
