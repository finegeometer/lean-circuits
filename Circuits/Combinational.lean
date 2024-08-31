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


namespace Circuit.Directed

def combinational {α β : 𝔽} (voltages : Voltages) (propagationDelay : ℝ) (f : (α → Bool) → (β → Bool)) : Directed α β :=
  Directed.ofPred fun input output =>
    (∀ b t, (output b t).2 = 0) →
    (∀ a t, (input a t).2 = 0) ∧
    ∀ (input' : α → Bool) (T : ℝ),
      (∀ a, ∀ t > T, voltages.VoltageIs (input' a) (input a t).1) →
      (∀ b, ∀ t > T + propagationDelay, voltages.VoltageIs (f input' b) (output b t).1)

theorem combinational_mono :
  delay1 ≤ delay2 → (combinational voltages delay1 f : Directed α β) ≤ combinational voltages delay2 f
:= by
  rw [le_def]
  intro leq input output H
  simp only [combinational, mem_ofPred] at *
  intro no_current_out; specialize H no_current_out
  constructor; exact H.1; obtain ⟨_,H⟩ := H
  intro input T inputs_eventually_correct x t pf; apply H input T inputs_eventually_correct x t
  linarith [pf]

theorem combinational_parallel
  {ι : 𝔽} {α β : ι → 𝔽} {propagationDelay : ℝ}
  {f : (i : ι) → (α i → Bool) → (β i → Bool)} :
  (parallel ι (fun i => combinational voltages propagationDelay (f i))) ≤
    combinational voltages propagationDelay (by exact fun input ⟨i,y⟩ => f i (fun x => input ⟨i,x⟩) y)
:= by
  rw [le_def]
  intro input output H
  simp only [Directed.mem_parallel, combinational, mem_ofPred] at H
  rw [combinational, mem_ofPred]; simp only
  intro no_current_out
  have:= fun i => H i (fun x => no_current_out ⟨i,x⟩)
  constructor; exact fun ⟨i,x⟩ => (this i).1 x
  intro input T input_eventually_correct ⟨i,x⟩
  exact (this i).2 (fun x => input ⟨i,x⟩) T (fun x => input_eventually_correct ⟨i,x⟩) x

open Classical
noncomputable local instance (priority := 2000) (α : Type) [Finite α] : Fintype α := Fintype.ofFinite α

theorem combinational_wire {α β : 𝔽} (f : α → β) :
  (wire (𝔽.Cospan.ofFwd f).reverse) ≤ combinational voltages 0 (fun input x => input (f x))
:= by
  rw [le_def]
  intro input output H
  rw [mem_wire] at H
  rw [combinational, mem_ofPred]; simp only
  intro no_current_out
  constructor
  · intro x t
    let S : Set β := {x}
    calc (input x t).2
      _ = ∑ x ∈ S, (input x t).2 := by simp [S]
      _ = ∑ x with _root_.id x ∈ S, (input x t).2 := by simp [Set.filter_mem_univ_eq_toFinset]
      _ = ∑ x with f x ∈ S, (output x t).2 := (H t).current S
      _ = ∑ x with f x ∈ S, 0 := by congr; funext; apply no_current_out
      _ = 0 := by simp
  · intro input T input_eventually_correct x t
    obtain ⟨v,H1,H2⟩ := (H t).1
    simp [𝔽.Cospan.reverse, 𝔽.Cospan.ofFwd] at H1 H2
    simp [<-H2, H1]
    apply input_eventually_correct

theorem Circuit.IsCombinational.series
  {α : Fin (Nat.succ n) → 𝔽} {propagationDelay : Fin n → ℝ}
  {f : (i : Fin n) → (α i.castSucc → Bool) → (α i.succ → Bool)} :
  (Circuit.Directed.series n α (fun i => Directed.combinational voltages (propagationDelay i) (f i))) ≤
    Directed.combinational voltages (∑ i, propagationDelay i) (Function.composeN (fun i => α i → Bool) f)
:= by
  rw [le_def]
  intro input output H
  simp only [mem_series, combinational, mem_ofPred] at H
  rw [combinational, mem_ofPred]; simp only
  intro no_current_out

  obtain ⟨bhvr,pf,H1,H2⟩ := H
  cases H1; cases H2

  have currents_zero : ∀ i x t, (bhvr i x t).2 = 0 := by
    apply Fin.reverseInduction
    · exact no_current_out
    · exact fun i IH => (pf i IH).1
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
    exact (pf i (currents_zero i.succ)).2 (Function.composeTo (fun i => α i → Bool) f i.castSucc input) (T + ∑ j : Fin n with j.castSucc < i.castSucc, propagationDelay j) IH x t $ calc
      t > _ := t_large
      _ = _ := by
        rw [<-Finset.sum_erase_add (a := i)]
        · rw [add_assoc]; congr
          ext j; simp only [Nat.succ_eq_add_one, Fin.castSucc_lt_succ_iff, Finset.mem_erase, ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Fin.castSucc_lt_castSucc_iff]
          rw [lt_iff_le_and_ne]; tauto
        · simp
