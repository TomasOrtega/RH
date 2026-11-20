import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IwLevel.CoprimeTors

/- English proof (translation)
Introduce `S A _ _ O _ ρ 𝔞 𝔟 hab K₁ K₂ K₃ i₁ i₂ i₃ _ _ _ h₁ h₂ h₃ d e he hK₃ hK₂`. Establish `h1mem : (1 : O) ∈ 𝔞 ⊔ 𝔟` using `hab ▸ Submodule.mem_top`. Take `⟨u, hu, v, hv, huv⟩` from `Submodule.mem_sup.1 h1mem`. Establish `k₁ : ∀ a ∈ 𝔞, i₁ ≫ ρ.act a = 1` using `fun a ha => (h₁ K₁ i₁).1 ⟨𝟙 _, Category.id_comp _⟩ a ha`. Establish `k₂ : ∀ a ∈ 𝔟, i₂ ≫ ρ.act a = 1` using `fun a ha => (h₂ K₂ i₂).1 ⟨𝟙 _, Category.id_comp _⟩ a ha`.

Establish `k₃ : ∀ a ∈ 𝔞 * 𝔟, i₃ ≫ ρ.act a = 1` using `fun a ha => (h₃ K₃ i₃).1 ⟨𝟙 _, Category.id_comp _⟩ a ha`. Establish `hadd : ∀ {T : Over S} (x : T ⟶ A) (a b : O), x ≫ ρ.act (a + b) = (x ≫ ρ.act a) * (x ≫ ρ.act b)` using `fun x a b => by`. Rewrite using `[ρ.map_add]`. Conclude with `MonObj.comp_mul x _ _`. Establish `hone : ∀ {T : Over S} (x : T ⟶ A), x ≫ ρ.act 1 = x` using `fun x => by`.

Rewrite using `[ρ.map_one, Category.comp_id]`. Establish `e₁ : i₁ ≫ ρ.act v = i₁`. Use `hadd i₁ v u` as an intermediate fact. Rewrite `this` using `[add_comm v u, huv, hone, k₁ u hu, _root_.mul_one]`. Conclude with `this.symm`.

Establish `e₂ : i₂ ≫ ρ.act u = i₂`. Use `hadd i₂ u v` as an intermediate fact. Rewrite `this` using `[huv, hone, k₂ v hv, _root_.mul_one]`. Conclude with `this.symm`. Establish `hm : GlobalTheory.IwLevel.KilledBy ρ (𝔞 * 𝔟) ((fst K₁ K₂ ≫ i₁) * (snd K₁ K₂ ≫ i₂))` using `fun c hc => by`.

Use `ρ.hom c` as an intermediate fact. Establish `hc₁ : c ∈ 𝔞` using `Ideal.mul_le_left (I := 𝔞) (J := 𝔟) hc`. Establish `hc₂ : c ∈ 𝔟` using `Ideal.mul_le_right (I := 𝔞) (J := 𝔟) hc`. Rewrite using `[MonObj.mul_comp, Category.assoc, Category.assoc, k₁ c hc₁, k₂ c hc₂, MonObj.comp_one, MonObj.comp_one, _root_.mul_one]`. Take `⟨m, hm'⟩` from `(h₃ _ _).2 hm`.

Establish `hg₁ : GlobalTheory.IwLevel.KilledBy ρ 𝔞 (i₃ ≫ ρ.act v)` using `fun a ha => by`. Rewrite using `[Category.assoc, ← ρ.map_mul]`. Conclude with `k₃ _ (Ideal.mul_mem_mul ha hv)`. Establish `hg₂ : GlobalTheory.IwLevel.KilledBy ρ 𝔟 (i₃ ≫ ρ.act u)` using `fun b hb => by`. Rewrite using `[Category.assoc, ← ρ.map_mul, mul_comm]`.

Conclude with `k₃ _ (Ideal.mul_mem_mul hu hb)`. Take `⟨g₁, hg₁'⟩` from `(h₁ _ _).2 hg₁`. Take `⟨g₂, hg₂'⟩` from `(h₂ _ _).2 hg₂`. Establish `iso : IsIso m`. Use `⟨⟨lift g₁ g₂, ?_, ?_⟩⟩` and prove the remaining obligations.

Establish `hr` using `ρ.hom v`. Establish `hs` using `ρ.hom u`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, lift_fst, Category.id_comp, ← cancel_mono i₁, Category.assoc, hg₁', ← Category.assoc, hm', MonObj.mul_comp, Category.assoc, Category.assoc, e₁, k₂ v hv, MonObj.comp_one, _root_.mul_one]`. Rewrite using `[Category.assoc, lift_snd, Category.id_comp, ← cancel_mono i₂, Category.assoc, hg₂', ← Category.assoc, hm', MonObj.mul_comp, Category.assoc, Category.assoc, e₂, k₁ u hu, MonObj.comp_one, _root_.one_mul]`.

Rewrite using `[← cancel_mono i₃, Category.assoc, hm', MonObj.comp_mul, ← Category.assoc, lift_fst, ← Category.assoc, lift_snd, hg₁', hg₂', ← hadd, add_comm, huv, hone, Category.id_comp]`. Establish `hP : GlobalTheory.IwLevel.IsIsogDeg (toUnit (K₁ ⊗ K₂)) (d * e)`. Rewrite using `[toUnit_unique (toUnit (K₁ ⊗ K₂)) (m ≫ toUnit K₃), ← _root_.one_mul (d * e)]`. Conclude with `(GlobalTheory.IwLevel.IsIsogDeg.of_isIso m).comp hK₃`. Apply the tactic sequence `have hpb : IsPullback (fst K₁ K₂) (snd K₁ K₂) (toUnit K₁) (toUnit K₂) := ⟨⟨toUnit_unique _ _⟩, ⟨PullbackCone.IsLimit.mk _ (fun c ↦ lift c.fst c.snd) (fun _ ↦ lift_fst _ _) (fun _ ↦ lift_snd _ _) fun c m h₁ h₂ ↦ by ext <;> simp [h₁, h₂]⟩⟩`.

Establish `hfst : GlobalTheory.IwLevel.IsIsogDeg (fst K₁ K₂) e` using `hK₂.of_isPullback (hpb.flip.map (Over.forget S))`. Establish `hcomp : fst K₁ K₂ ≫ toUnit K₁ = toUnit (K₁ ⊗ K₂)` using `toUnit_unique _ _`. Use `hfst.fin` as an intermediate fact. Use `hfst.flat` as an intermediate fact. Use `hfst.surj` as an intermediate fact.

Use `hP.fin` as an intermediate fact. Use `hP.flat` as an intermediate fact. Use `hP.surj` as an intermediate fact. Take `⟨t, -⟩` from `(h₂ K₁ (1 : K₁ ⟶ A)).2 fun b _ => by have := ρ.hom b; exact MonObj.one_comp _`. Set `s : K₁ ⟶ K₁ ⊗ K₂` to `lift (𝟙 K₁) t`.

Establish `hs : s ≫ fst K₁ K₂ = 𝟙 K₁` using `lift_fst _ _`. Establish `hsep : IsSeparated (fst K₁ K₂).left` using `inferInstance`. Establish `: IsFinite (s.left ≫ (fst K₁ K₂).left)`. Rewrite using `[← Over.comp_left, hs, Over.id_left]`. Use `infer_instance`.

Establish `: IsFinite s.left` using `IsFinite.of_comp s.left (fst K₁ K₂).left`. Establish `hsu : s ≫ toUnit (K₁ ⊗ K₂) = toUnit K₁` using `toUnit_unique _ _`. Establish `hfin : IsFinite (toUnit K₁).left` using `by rw [← hsu, Over.comp_left]; infer_instance`. Establish `: Flat ((fst K₁ K₂).left ≫ (toUnit K₁).left)` using `by rw [← Over.comp_left, hcomp]; infer_instance`. Establish `hflat : Flat (toUnit K₁).left` using `flat_of_comp_of_flat_of_surjective (fst K₁ K₂).left _`.

Establish `: Surjective ((fst K₁ K₂).left ≫ (toUnit K₁).left)`. Rewrite using `[← Over.comp_left, hcomp]`. Use `infer_instance`. Establish `hsurj : Surjective (toUnit K₁).left` using `Surjective.of_comp (fst K₁ K₂).left _`. Use `⟨hfin, hflat, hsurj, fun y => ?_⟩` and prove the remaining obligations.

Establish `h` using `GlobalTheory.FinrankComp.finrank_comp_of_const (fst K₁ K₂).left (toUnit K₁).left e hfst.rank y`. Rewrite `h` using `[← Over.comp_left, hcomp, hP.rank, mul_comm d e]`. Conclude with `(Nat.eq_of_mul_eq_mul_left he h).symm`.
-/
theorem isIsogDeg_of_coprime : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [CommRing O]
    (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct A O) (𝔞 𝔟 : Ideal O), 𝔞 ⊔ 𝔟 = ⊤ →
    ∀ (K₁ K₂ K₃ : Over S) (i₁ : K₁ ⟶ A) (i₂ : K₂ ⟶ A) (i₃ : K₃ ⟶ A), Mono i₁ → Mono i₂ → Mono i₃ →
    (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₁ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔞 x) →
    (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₂ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔟 x) →
    (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₃ x ↔ GlobalTheory.IwLevel.KilledBy ρ (𝔞 * 𝔟) x) →
    ∀ (d e : ℕ), 0 < e → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₃) (d * e) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₂) e →
    GlobalTheory.IwLevel.IsIsogDeg (toUnit K₁) d := by
  intro S A _ _ O _ ρ 𝔞 𝔟 hab K₁ K₂ K₃ i₁ i₂ i₃ _ _ _ h₁ h₂ h₃ d e he hK₃ hK₂
  have h1mem : (1 : O) ∈ 𝔞 ⊔ 𝔟 := hab ▸ Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1mem
  have k₁ : ∀ a ∈ 𝔞, i₁ ≫ ρ.act a = 1 := fun a ha => (h₁ K₁ i₁).1 ⟨𝟙 _, Category.id_comp _⟩ a ha
  have k₂ : ∀ a ∈ 𝔟, i₂ ≫ ρ.act a = 1 := fun a ha => (h₂ K₂ i₂).1 ⟨𝟙 _, Category.id_comp _⟩ a ha
  have k₃ : ∀ a ∈ 𝔞 * 𝔟, i₃ ≫ ρ.act a = 1 := fun a ha => (h₃ K₃ i₃).1 ⟨𝟙 _, Category.id_comp _⟩ a ha
  have hadd : ∀ {T : Over S} (x : T ⟶ A) (a b : O),
      x ≫ ρ.act (a + b) = (x ≫ ρ.act a) * (x ≫ ρ.act b) := fun x a b => by
    rw [ρ.map_add]; exact MonObj.comp_mul x _ _
  have hone : ∀ {T : Over S} (x : T ⟶ A), x ≫ ρ.act 1 = x := fun x => by
    rw [ρ.map_one, Category.comp_id]
  have e₁ : i₁ ≫ ρ.act v = i₁ := by
    have := hadd i₁ v u
    rw [add_comm v u, huv, hone, k₁ u hu, _root_.mul_one] at this
    exact this.symm
  have e₂ : i₂ ≫ ρ.act u = i₂ := by
    have := hadd i₂ u v
    rw [huv, hone, k₂ v hv, _root_.mul_one] at this
    exact this.symm
  have hm : GlobalTheory.IwLevel.KilledBy ρ (𝔞 * 𝔟) ((fst K₁ K₂ ≫ i₁) * (snd K₁ K₂ ≫ i₂)) := fun c hc => by
    have := ρ.hom c
    have hc₁ : c ∈ 𝔞 := Ideal.mul_le_left (I := 𝔞) (J := 𝔟) hc
    have hc₂ : c ∈ 𝔟 := Ideal.mul_le_right (I := 𝔞) (J := 𝔟) hc
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, k₁ c hc₁, k₂ c hc₂, MonObj.comp_one,
      MonObj.comp_one, _root_.mul_one]
  obtain ⟨m, hm'⟩ := (h₃ _ _).2 hm
  have hg₁ : GlobalTheory.IwLevel.KilledBy ρ 𝔞 (i₃ ≫ ρ.act v) := fun a ha => by
    rw [Category.assoc, ← ρ.map_mul]; exact k₃ _ (Ideal.mul_mem_mul ha hv)
  have hg₂ : GlobalTheory.IwLevel.KilledBy ρ 𝔟 (i₃ ≫ ρ.act u) := fun b hb => by
    rw [Category.assoc, ← ρ.map_mul, mul_comm]; exact k₃ _ (Ideal.mul_mem_mul hu hb)
  obtain ⟨g₁, hg₁'⟩ := (h₁ _ _).2 hg₁
  obtain ⟨g₂, hg₂'⟩ := (h₂ _ _).2 hg₂
  have iso : IsIso m := by
    refine ⟨⟨lift g₁ g₂, ?_, ?_⟩⟩
    · have hr := ρ.hom v
      have hs := ρ.hom u
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, Category.id_comp, ← cancel_mono i₁, Category.assoc, hg₁',
          ← Category.assoc, hm', MonObj.mul_comp, Category.assoc, Category.assoc, e₁, k₂ v hv,
          MonObj.comp_one, _root_.mul_one]
      · rw [Category.assoc, lift_snd, Category.id_comp, ← cancel_mono i₂, Category.assoc, hg₂',
          ← Category.assoc, hm', MonObj.mul_comp, Category.assoc, Category.assoc, e₂, k₁ u hu,
          MonObj.comp_one, _root_.one_mul]
    · rw [← cancel_mono i₃, Category.assoc, hm', MonObj.comp_mul, ← Category.assoc, lift_fst,
        ← Category.assoc, lift_snd, hg₁', hg₂', ← hadd, add_comm, huv, hone, Category.id_comp]
  have hP : GlobalTheory.IwLevel.IsIsogDeg (toUnit (K₁ ⊗ K₂)) (d * e) := by
    rw [toUnit_unique (toUnit (K₁ ⊗ K₂)) (m ≫ toUnit K₃), ← _root_.one_mul (d * e)]
    exact (GlobalTheory.IwLevel.IsIsogDeg.of_isIso m).comp hK₃
  have hpb : IsPullback (fst K₁ K₂) (snd K₁ K₂) (toUnit K₁) (toUnit K₂) :=
    ⟨⟨toUnit_unique _ _⟩, ⟨PullbackCone.IsLimit.mk _ (fun c ↦ lift c.fst c.snd) (fun _ ↦ lift_fst _ _)
      (fun _ ↦ lift_snd _ _) fun c m h₁ h₂ ↦ by ext <;> simp [h₁, h₂]⟩⟩
  have hfst : GlobalTheory.IwLevel.IsIsogDeg (fst K₁ K₂) e := hK₂.of_isPullback (hpb.flip.map (Over.forget S))
  have hcomp : fst K₁ K₂ ≫ toUnit K₁ = toUnit (K₁ ⊗ K₂) := toUnit_unique _ _
  have := hfst.fin; have := hfst.flat; have := hfst.surj
  have := hP.fin; have := hP.flat; have := hP.surj

  obtain ⟨t, -⟩ := (h₂ K₁ (1 : K₁ ⟶ A)).2 fun b _ => by have := ρ.hom b; exact MonObj.one_comp _
  let s : K₁ ⟶ K₁ ⊗ K₂ := lift (𝟙 K₁) t
  have hs : s ≫ fst K₁ K₂ = 𝟙 K₁ := lift_fst _ _
  have hsep : IsSeparated (fst K₁ K₂).left := inferInstance
  have : IsFinite (s.left ≫ (fst K₁ K₂).left) := by
    rw [← Over.comp_left, hs, Over.id_left]; infer_instance
  have : IsFinite s.left := IsFinite.of_comp s.left (fst K₁ K₂).left
  have hsu : s ≫ toUnit (K₁ ⊗ K₂) = toUnit K₁ := toUnit_unique _ _
  have hfin : IsFinite (toUnit K₁).left := by rw [← hsu, Over.comp_left]; infer_instance
  have : Flat ((fst K₁ K₂).left ≫ (toUnit K₁).left) := by rw [← Over.comp_left, hcomp]; infer_instance
  have hflat : Flat (toUnit K₁).left := flat_of_comp_of_flat_of_surjective (fst K₁ K₂).left _
  have : Surjective ((fst K₁ K₂).left ≫ (toUnit K₁).left) := by
    rw [← Over.comp_left, hcomp]; infer_instance
  have hsurj : Surjective (toUnit K₁).left := Surjective.of_comp (fst K₁ K₂).left _
  refine ⟨hfin, hflat, hsurj, fun y => ?_⟩
  have h := GlobalTheory.FinrankComp.finrank_comp_of_const (fst K₁ K₂).left (toUnit K₁).left e hfst.rank y
  rw [← Over.comp_left, hcomp, hP.rank, mul_comm d e] at h
  exact (Nat.eq_of_mul_eq_mul_left he h).symm

end GlobalTheory.IwLevel.CoprimeTors
