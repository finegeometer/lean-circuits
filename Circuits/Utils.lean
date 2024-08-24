import Batteries.Data.Sum.Basic
import Mathlib.Data.Finite.Basic

def Coequalizer (f g : α → β) : Type := @Quot β (fun a b => ∃ x, a = f x ∧ b = g x)
def Coequalizer.inj {f g : α → β} : β → Coequalizer f g := Quot.mk _
def Coequalizer.lift {f g : α → β} (h : β → γ) (pf : (a : α) → h (f a) = h (g a)) (x : Coequalizer f g) : γ :=
  Quot.lift h (fun b c ⟨a, p, q⟩ => by rw [p,q,pf]) x
def Coequalizer.ind {f g : α → β} {P : Coequalizer f g → Prop} : (∀x, P (Coequalizer.inj x)) → (∀x, P x) := Quot.ind
theorem Coequalizer.sound {f g : α → β} (x : α) : @Eq (Coequalizer f g) (Coequalizer.inj (f x)) (Coequalizer.inj (g x)) := by apply Quot.sound; exists x
instance Coequalizer.finite [Finite β] {f g : α → β} : Finite (Coequalizer f g) := Quot.finite _
theorem Coequalizer.lift_inj : Coequalizer.lift h pf (Coequalizer.inj x) = h x := by unfold lift inj; simp [Quot.lift_mk]


def Pushout (f : α → β) (g : α → γ) : Type := Coequalizer (Sum.inl ∘ f) (Sum.inr ∘ g)
def Pushout.inl {f : α → β} {g : α → γ} (x : β) : Pushout f g := Coequalizer.inj (Sum.inl x)
def Pushout.inr {f : α → β} {g : α → γ} (x : γ) : Pushout f g := Coequalizer.inj (Sum.inr x)
def Pushout.lift {f : α → β} {g : α → γ} (h₁ : β → δ) (h₂ : γ → δ) (pf : (a : α) → h₁ (f a) = h₂ (g a)) (x : Pushout f g) : δ :=
  Coequalizer.lift (Sum.elim h₁ h₂) pf x
theorem Pushout.ind (P : Pushout f g → Prop) (H1 : ∀ x, P (Pushout.inl x)) (H2 : ∀ x, P (Pushout.inr x)) : ∀ x, P x := by
  apply Coequalizer.ind; apply Sum.rec; exact H1; exact H2
theorem Pushout.sound {f : α → β} {g : α → γ} (x : α) : @Eq (Pushout f g) (Pushout.inl (f x)) (Pushout.inr (g x)) := by apply Coequalizer.sound
instance Pushout.finite [Finite β] [Finite γ] {f : α → β} {g : α → γ} : Finite (Pushout f g) := Coequalizer.finite
theorem Pushout.lift_inl : Pushout.lift f g pf (Pushout.inl x) = f x := by unfold lift inl; simp [Coequalizer.lift_inj]
theorem Pushout.lift_inr : Pushout.lift f g pf (Pushout.inr x) = g x := by unfold lift inr; simp [Coequalizer.lift_inj]


structure 𝔽 : Type 1 where
  T : Type
  [finite : Finite T]

@[reducible] instance : CoeSort 𝔽 Type where coe := 𝔽.T
instance {α : 𝔽} : Finite α := α.finite
instance [Finite α] : CoeDep Type α 𝔽 where coe := ⟨α⟩

structure 𝔽.Cospan (α β : 𝔽) : Type 1 where
  center : 𝔽
  fwd : α → center
  bwd : β → center

def 𝔽.Cospan.id : Cospan α α := ⟨α, _root_.id, _root_.id⟩
def 𝔽.Cospan.comp (f : 𝔽.Cospan α β) (g : 𝔽.Cospan β γ) : 𝔽.Cospan α γ where
  center := Pushout f.bwd g.fwd
  fwd := Pushout.inl ∘ f.fwd
  bwd := Pushout.inr ∘ g.bwd
def 𝔽.Cospan.merge [Finite ι] {α β : ι → 𝔽} (f : (i : ι) → 𝔽.Cospan (α i) (β i)) : 𝔽.Cospan ((i : ι) × α i) ((i : ι) × β i) where
  center := (i : ι) × (f i).center
  fwd := Sigma.map _root_.id (fun i a => (f i).fwd a)
  bwd := Sigma.map _root_.id (fun i a => (f i).bwd a)

def 𝔽.Cospan.ofFwd {α β : 𝔽} (f : α → β) : 𝔽.Cospan α β := ⟨β, f, _root_.id⟩
abbrev 𝔽.Cospan.ofEquiv {α β : 𝔽} (f : α ≃ β) : 𝔽.Cospan α β := 𝔽.Cospan.ofFwd f


structure 𝔽.Cospan.Equiv (f g : Cospan α β) where
  center : f.center ≃ g.center
  fwd : center ∘ f.fwd = g.fwd
  bwd : center ∘ f.bwd = g.bwd

def 𝔽.Cospan.Equiv.refl (f : Cospan α α) : f.Equiv f := ⟨_root_.Equiv.refl _, rfl, rfl⟩
def 𝔽.Cospan.Equiv.symm {f g : Cospan α β} (e : f.Equiv g) : g.Equiv f where
  center := e.center.symm
  fwd := by rw [<-e.fwd, <-Function.comp.assoc]; simp
  bwd := by rw [<-e.bwd, <-Function.comp.assoc]; simp
def 𝔽.Cospan.Equiv.trans {f g h : Cospan α β} (e1 : f.Equiv g) (e2 : g.Equiv h) : f.Equiv h where
  center := e1.center.trans e2.center
  fwd := by rw [<-e2.fwd, <-e1.fwd]; rfl
  bwd := by rw [<-e2.bwd, <-e1.bwd]; rfl

instance : Trans (@𝔽.Cospan.Equiv α β) (@𝔽.Cospan.Equiv α β) (@𝔽.Cospan.Equiv α β) where
  trans := 𝔽.Cospan.Equiv.trans

def 𝔽.Cospan.id_ofFwd {α : 𝔽} : Equiv (ofFwd (fun x : α => x)) id := Equiv.refl _
def 𝔽.Cospan.comp_ofFwd {α β γ : 𝔽} (f : α → β) (g : β → γ) : Equiv (ofFwd (g ∘ f)) (comp (ofFwd f) (ofFwd g)) where
  center.toFun := Pushout.inr
  center.invFun := Pushout.lift g _root_.id (fun _ => rfl)
  center.left_inv := by simp [Function.LeftInverse, Pushout.lift_inr]
  center.right_inv := by
    apply Pushout.ind <;> intro _
    · symm; apply Pushout.sound
    · rfl
  fwd := by funext a; simp [ofFwd, comp, <-Pushout.sound (g := g)]
  bwd := rfl

def 𝔽.Cospan.comp.assoc {α β γ δ : 𝔽} (f : Cospan α β) (g : Cospan β γ) (h : Cospan γ δ) :
  ((f.comp g).comp h).Equiv (f.comp (g.comp h))
where
  center.toFun := Pushout.lift (Pushout.lift Pushout.inl (Pushout.inr ∘ Pushout.inl) (by apply Pushout.sound)) (Pushout.inr ∘ Pushout.inr) $ by intro; change Pushout.inr _ = Pushout.inr _; congr; apply Pushout.sound
  center.invFun := Pushout.lift (Pushout.inl ∘ Pushout.inl) (Pushout.lift (Pushout.inl ∘ Pushout.inr) Pushout.inr (by apply Pushout.sound)) $ by intro; change Pushout.inl _ = Pushout.inl _; congr; apply Pushout.sound
  center.left_inv := by
    apply Pushout.ind
    apply Pushout.ind
    intro; rfl
    intro; rfl
    intro; rfl
  center.right_inv := by
    apply Pushout.ind
    intro; rfl
    apply Pushout.ind
    intro; rfl
    intro; rfl
  fwd := rfl
  bwd := rfl

def 𝔽.Cospan.comp.lunit {α β : 𝔽} (f : Cospan α β) : (id.comp f).Equiv f where
  center.toFun := Pushout.lift f.fwd _root_.id $ by intro; rfl
  center.invFun := Pushout.inr
  center.left_inv := by
    apply Pushout.ind
    intro; symm; apply Pushout.sound
    intro; rfl
  center.right_inv := by intro; rfl
  fwd := rfl
  bwd := rfl

def 𝔽.Cospan.comp.runit {α β : 𝔽} (f : Cospan α β) : (f.comp id).Equiv f where
  center.invFun := Pushout.inl
  center.toFun := Pushout.lift _root_.id f.bwd $ by intro; rfl
  center.left_inv := by
    apply Pushout.ind
    intro; rfl
    intro; apply Pushout.sound
  center.right_inv := by intro; rfl
  fwd := rfl
  bwd := rfl

def 𝔽.Cospan.congr_comp {α β γ : 𝔽} (f g : Cospan α β) (h : Cospan β γ)
  (H : f.Equiv g) : (f.comp h).Equiv (g.comp h)
where
  center.toFun := Pushout.lift (Pushout.inl ∘ H.center) Pushout.inr $ by intro; change (_ ∘ _ ∘ f.bwd) _ = _; rw [H.bwd]; apply Pushout.sound
  center.invFun := Pushout.lift (Pushout.inl ∘ H.center.symm) Pushout.inr $ by intro; change (_ ∘ _ ∘ g.bwd) _ = _; rw [<-H.bwd]; simp only [Function.comp_apply, Equiv.symm_apply_apply]; apply Pushout.sound
  center.left_inv := by
    apply Pushout.ind
    · intro; change Pushout.inl _ = _; simp
    · intro; rfl
  center.right_inv := by
    apply Pushout.ind
    · intro; change Pushout.inl _ = _; simp
    · intro; rfl
  fwd := by funext; change Pushout.inl _ = Pushout.inl _; rw [<-H.fwd]; rfl
  bwd := by funext; rfl






def Equiv.unitSigma (α : Unit → Type) : (i : Unit) × α i ≃ α () where
  toFun := Sigma.snd
  invFun := Sigma.mk ()
  left_inv _ := rfl
  right_inv _ := rfl
