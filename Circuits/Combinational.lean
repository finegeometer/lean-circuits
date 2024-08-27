import «Circuits».Circuit.Directed

structure Voltages where
  min : ℝ
  lo : ℝ
  hi : ℝ
  max : ℝ
def Voltages.sane (voltages : Voltages) :=
  voltages.min < voltages.lo ∧
  voltages.lo < voltages.hi ∧
  voltages.hi < voltages.max
def Voltages.VoltageIs (voltages : Voltages) (x : Bool) (V : ℝ) : Prop :=
  if x
  then V ∈ Set.Icc voltages.hi voltages.max
  else V ∈ Set.Icc voltages.min voltages.lo


def Circuit.Directed.IsCombinational {α β : 𝔽} (circ : Circuit.Directed α β)
  (voltages : Voltages) (propagationDelay : ℝ) (f : (α → Bool) → (β → Bool)) : Prop
:= ∀ bhvr ∈ circ,
  (∀ b t, (bhvr.2 b t).2 = 0) →
  (∀ a t, (bhvr.1 a t).2 = 0) ∧
  ∀ (input : α → Bool) (T : ℝ),
    (∀ a, ∀ t > T, voltages.VoltageIs (input a) (bhvr.1 a t).1) →
    (∀ b, ∀ t > T + propagationDelay, voltages.VoltageIs (f input b) (bhvr.2 b t).1)



open Classical
noncomputable local instance (priority := 2000) (α : Type) [Finite α] : Fintype α := Fintype.ofFinite α

theorem Circuit.IsCombinational.series
  {α : Fin (Nat.succ n) → 𝔽} {c : (i : Fin n) → Circuit.Directed (α i.castSucc) (α i.succ)}
  {propagationDelay : Fin n → ℝ}
  {f : (i : Fin n) → (α i.castSucc → Bool) → (α i.succ → Bool)}
  (H : ∀ i, (c i).IsCombinational voltages (propagationDelay i) (f i)) :
  (Circuit.Directed.series n α c).IsCombinational voltages (∑ i, propagationDelay i)
    (Function.composeN (fun i => α i → Bool) f)
:= by
  intro ⟨input,output⟩ pf zero_current_out
  rw [Circuit.Directed.mem_series] at pf

  obtain ⟨bhvr,pf,H1,H2⟩ := pf
  cases H1; cases H2

  have currents_zero : ∀ i x t, (bhvr i x t).2 = 0 := by
    apply Fin.reverseInduction
    · exact zero_current_out
    · exact fun i IH => (H i (bhvr i.castSucc, bhvr i.succ) (pf i) IH).1
  constructor; exact currents_zero 0

  intro input T base_case

  suffices ∀ (i : Fin n.succ) (b : α i),
    ∀ t > T + ∑ j : Fin n with j.castSucc < i, propagationDelay j,
      voltages.VoltageIs (Function.composeTo (fun i => α i → Bool) f i input b) (bhvr i b t).1
  by
    specialize this (Fin.last n); revert this
    suffices Finset.filter (fun j : Fin n => j.castSucc < Fin.last n) Finset.univ = Finset.univ by rw [this]; exact _root_.id
    ext i; simp [Fin.castSucc_lt_last]

  apply Fin.induction
  · suffices ∑ j : Fin n with j.castSucc < 0, propagationDelay j = 0 by rw [this, add_zero]; exact base_case
    apply Finset.sum_eq_zero; simp
  · intro i IH x t t_large
    rw [Function.composeTo.step]
    exact (H i (bhvr i.castSucc, bhvr i.succ) (pf i) (currents_zero i.succ)).2 (Function.composeTo (fun i => α i → Bool) f i.castSucc input) (T + ∑ j : Fin n with j.castSucc < i.castSucc, propagationDelay j) IH x t $ calc
      t > _ := t_large
      _ = _ := by
        rw [<-Finset.sum_erase_add (a := i)]
        · rw [add_assoc]; congr
          ext j; simp only [Nat.succ_eq_add_one, Fin.castSucc_lt_succ_iff, Finset.mem_erase, ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Fin.castSucc_lt_castSucc_iff]
          rw [lt_iff_le_and_ne]; tauto
        · simp
