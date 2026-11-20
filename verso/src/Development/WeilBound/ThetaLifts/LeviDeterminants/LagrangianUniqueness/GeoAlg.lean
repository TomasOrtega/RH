import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open Matrix GlobalTheory.WeilM Module

namespace PositivityTheory.ThKF0.Geo

section Form

variable {F : Type} [Field F] {κ : Type} [Fintype κ]

def om (F : Type) [Field F] (κ : Type) [Fintype κ] : LinearMap.BilinForm F ((κ → F) × (κ → F)) :=
  LinearMap.mk₂ F (fun w w' => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem om_apply (w w' : (κ → F) × (κ → F)) : om F κ w w' = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 := rfl

/- English proof (translation)
Establish `h1 : ∀ i, w.2 i = 0` using `fun i => by`. Use `h (Pi.single i 1, 0)` as an intermediate fact. Simplify `this` using `[om_apply, single_dotProduct]`. Establish `h2 : ∀ i, w.1 i = 0` using `fun i => by`. Use `h (0, Pi.single i 1)` as an intermediate fact.

Simplify `this` using `[om_apply, dotProduct_single]`. Conclude with `Prod.ext (funext h2) (funext h1)`.
-/
theorem eq_zero_of_om (w : (κ → F) × (κ → F)) (h : ∀ w', om F κ w' w = 0) : w = 0 := by
  classical
  have h1 : ∀ i, w.2 i = 0 := fun i => by
    have := h (Pi.single i 1, 0)
    simpa [om_apply, single_dotProduct] using this
  have h2 : ∀ i, w.1 i = 0 := fun i => by
    have := h (0, Pi.single i 1)
    simpa [om_apply, dotProduct_single] using this
  exact Prod.ext (funext h2) (funext h1)

/- English proof (translation)
Introduce `x y h` and use `by rw [om_apply] at h ⊢ linear_combination -h`.
-/
theorem om_refl : (om F κ).IsRefl := fun x y h => by
  rw [om_apply] at h ⊢
  linear_combination -h

/- English proof (translation)
Establish `hiso : L ≤ (om F κ).orthogonal L`. Introduce `x hx`. Rewrite using `[LinearMap.BilinForm.mem_orthogonal_iff]`. Introduce `y hy`. Rewrite using `[om_apply, h y hy x hx, sub_self]`.

Establish `hbot : (L ⊓ (om F κ).orthogonal ⊤ : Submodule F ((κ → F) × (κ → F))) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite using `[Submodule.mem_bot]`. Apply `eq_zero_of_om` to reduce the goal to its premises.

Introduce `w'`. Conclude with `(LinearMap.BilinForm.mem_orthogonal_iff.mp hx.2) w' Submodule.mem_top`. Establish `hdim` using `LinearMap.BilinForm.finrank_add_finrank_orthogonal (om_refl (F := F) (κ := κ)) L`. Rewrite `hdim` using `[hbot, finrank_bot, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hr]`. Establish `heq : L = (om F κ).orthogonal L` using `Submodule.eq_of_le_of_finrank_eq hiso (by rw [hr]; omega)`.

Prove the components needed by the constructor for the conclusion. Introduce `ha`. Conclude with `h a ha`. Introduce `ha`. Rewrite using `[heq, LinearMap.BilinForm.mem_orthogonal_iff]`.

Introduce `y hy`. Rewrite using `[om_apply, ha y hy, sub_self]`.
-/
theorem lag_of_finrank (L : Submodule F ((κ → F) × (κ → F))) (h : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (hr : finrank F L = Fintype.card κ) (a) : a ∈ L ↔ ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
  have hiso : L ≤ (om F κ).orthogonal L := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [om_apply, h y hy x hx, sub_self]
  have hbot : (L ⊓ (om F κ).orthogonal ⊤ : Submodule F ((κ → F) × (κ → F))) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    apply eq_zero_of_om
    intro w'
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx.2) w' Submodule.mem_top
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal (om_refl (F := F) (κ := κ)) L
  rw [hbot, finrank_bot, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hr] at hdim
  have heq : L = (om F κ).orthogonal L := Submodule.eq_of_le_of_finrank_eq hiso (by rw [hr]; omega)
  constructor
  · intro ha
    exact h a ha
  · intro ha
    rw [heq, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [om_apply, ha y hy, sub_self]

end Form

section Abs

variable {F : Type} [Field F] {A : Type} [CommRing A] [Algebra F A]

variable (A) in

def emb (κ : Type) : ((κ → F) × (κ → F)) →ₗ[F] ((κ → A) × (κ → A)) :=
  ((Algebra.linearMap F A).compLeft κ).prodMap ((Algebra.linearMap F A).compLeft κ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem emb_apply {κ : Type} (w : (κ → F) × (κ → F)) :
    emb A κ w = (fun i => algebraMap F A (w.1 i), fun i => algebraMap F A (w.2 i)) := rfl

/- English proof (translation)
Introduce `a b hab`. Rewrite `hab` using `[emb_apply, emb_apply]`. Simplify using `only [Prod.mk.injEq] at hab`. Conclude with `Prod.ext (funext fun i => hA (congrFun hab.1 i)) (funext fun i => hA (congrFun hab.2 i))`.
-/
theorem emb_inj (hA : Function.Injective (algebraMap F A)) {κ : Type} : Function.Injective (emb (F := F) A κ) := by
  intro a b hab
  rw [emb_apply, emb_apply] at hab
  simp only [Prod.mk.injEq] at hab
  exact Prod.ext (funext fun i => hA (congrFun hab.1 i)) (funext fun i => hA (congrFun hab.2 i))

/- English proof (translation)
Simplify using `[emb_apply, om_apply, dotProduct]`.
-/
theorem emb_form {κ : Type} [Fintype κ] (a b : (κ → F) × (κ → F)) :
    (emb A κ a).1 ⬝ᵥ (emb A κ b).2 - (emb A κ b).1 ⬝ᵥ (emb A κ a).2 = algebraMap F A (om F κ a b) := by
  simp [emb_apply, om_apply, dotProduct]

variable {VA : Type} [AddCommGroup VA] [Module A VA] [Module F VA] [IsScalarTower F A VA] {BA : VA → VA → A}
  {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module F V]

/- English proof (translation)
Use `choose f hf using hr`. Use `⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, hf⟩` and prove the remaining obligations. Introduce `x y`. Apply `emb_inj hA` to reduce the goal to its premises. Rewrite using `[map_add, ← hf, ← hf, ← hf, map_add, map_add]`.

Introduce `c x`. Apply `emb_inj hA` to reduce the goal to its premises. Rewrite using `[RingHom.id_apply, map_smul, ← hf, ← hf, map_smul]`. Conclude with `co.e.toLinearMap.map_smul_of_tower c (inc x)`.
-/
theorem exists_coord (hA : Function.Injective (algebraMap F A)) (co : Darboux BA κ) (inc : V →ₗ[F] VA)
    (hr : ∀ x, ∃ w, co.e (inc x) = emb (F := F) A κ w) :
    ∃ r : V →ₗ[F] (κ → F) × (κ → F), ∀ x, co.e (inc x) = emb A κ (r x) := by
  choose f hf using hr
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, hf⟩
  · intro x y
    apply emb_inj hA
    rw [map_add, ← hf, ← hf, ← hf, map_add, map_add]
  · intro c x
    apply emb_inj hA
    rw [RingHom.id_apply, map_smul, ← hf, ← hf, map_smul]
    exact co.e.toLinearMap.map_smul_of_tower c (inc x)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `e1 : x ⬝ᵥ (a + b).2 + ⅟(2 : A) * ((a + b).1 ⬝ᵥ (a + b).2) = (x ⬝ᵥ a.2 + ⅟(2 : A) * (a.1 ⬝ᵥ a.2)) + ((x + a.1) ⬝ᵥ b.2 + ⅟(2 : A) * (b.1 ⬝ᵥ b.2))`. Establish `h2 : ⅟(2 : A) * 2 = 1` using `invOf_mul_self 2`. Simplify using `only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]`. Take the linear combination `(-⅟(2 : A)) * h + (a.1 ⬝ᵥ b.2) * h2`.

Establish `e2 : x + (a + b).1 = x + a.1 + b.1` using `by rw [Prod.fst_add, add_assoc]`. Simplify using `only [schr]`. Rewrite using `[e1, e2, AddChar.map_add_eq_mul, mul_assoc]`.
-/
theorem schr_add [Invertible (2 : A)] (ψ : AddChar A ℂ) (a b : (κ → A) × (κ → A))
    (h : a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 = 0) (φ : (κ → A) → ℂ) : schr ψ (a + b) φ = schr ψ a (schr ψ b φ) := by
  funext x
  have e1 : x ⬝ᵥ (a + b).2 + ⅟(2 : A) * ((a + b).1 ⬝ᵥ (a + b).2) =
      (x ⬝ᵥ a.2 + ⅟(2 : A) * (a.1 ⬝ᵥ a.2)) + ((x + a.1) ⬝ᵥ b.2 + ⅟(2 : A) * (b.1 ⬝ᵥ b.2)) := by
    have h2 : ⅟(2 : A) * 2 = 1 := invOf_mul_self 2
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    linear_combination (-⅟(2 : A)) * h + (a.1 ⬝ᵥ b.2) * h2
  have e2 : x + (a + b).1 = x + a.1 + b.1 := by rw [Prod.fst_add, add_assoc]
  simp only [schr]
  rw [e1, e2, AddChar.map_add_eq_mul, mul_assoc]

variable {VB : Type} [AddCommGroup VB] [Module A VB] [Module F VB] [IsScalarTower F A VB] {BB : VB → VB → A}
  {κ₁ : Type} [Fintype κ₁] {V₁ : Type} [AddCommGroup V₁] [Module F V₁] {U : Type} [AddCommGroup U] [Module F U]

/- English proof (translation)
Take `⟨r, hr'⟩` from `exists_coord hA co inc hr`. Take `⟨r₁, hr₁'⟩` from `exists_coord hA co₁ inc₁ hr₁`. Establish `hBx : ∀ x y, BA (inc x) (inc y) = algebraMap F A (om F κ (r x) (r y))` using `fun x y => by`. Rewrite using `[co.form, hr', hr', emb_form]`. Establish `hBz : ∀ z z', BB (inc₁ z) (inc₁ z') = algebraMap F A (om F κ₁ (r₁ z) (r₁ z'))` using `fun z z' => by`.

Rewrite using `[co₁.form, hr₁', hr₁', emb_form]`. Establish `hBA0 : ∀ w, BA w 0 = 0` using `fun w => by`. Rewrite using `[co.form]`. Simplify using the standard rewrite rules. Establish `hrinj : Function.Injective r`.

Introduce `a b hab`. Apply `hinc` to reduce the goal to its premises. Apply `co.e.injective` to reduce the goal to its premises. Rewrite using `[hr', hr', hab]`. Establish `hr₁inj : Function.Injective r₁`.

Introduce `a b hab`. Apply `hinc₁` to reduce the goal to its premises. Apply `co₁.e.injective` to reduce the goal to its premises. Rewrite using `[hr₁', hr₁', hab]`. Establish `hr₁surj : Function.Surjective r₁`.

Use `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := r₁) ?_).mp hr₁inj` and prove the remaining obligations. Rewrite using `[hd₁, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]`. Expand and normalize the polynomial expressions, which then agree. Set `L₁ : Submodule F V₁` to `LinearMap.ker ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁)`. Establish `hL₁ : ∀ z, z ∈ L₁ ↔ (r₁ z).1 = 0` using `fun z => by`.

Simplify using `[L₁]`. Establish `hfinL₁ : finrank F L₁ = Fintype.card κ₁`. Establish `hsurj : Function.Surjective ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁)` using `fun v => by`. Take `⟨x, hx⟩` from `hr₁surj (v, 0)`. Conclude with `⟨x, by simp [hx]⟩`.

Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁)`. Rewrite `hrn` using `[LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, hd₁]`. Establish `e : finrank F L₁ = finrank F (LinearMap.ker ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁))` using `rfl`. Use linear arithmetic over natural numbers and integers. Establish `hjinj : Function.Injective j`.

Use `(injective_iff_map_eq_zero j).mpr fun z hz => ?_` and prove the remaining obligations. Apply `hr₁inj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply `eq_zero_of_om` to reduce the goal to its premises. Introduce `v`.

Take `⟨z', rfl⟩` from `hr₁surj v`. Apply `hA` to reduce the goal to its premises. Rewrite using `[← hBz, ← hB, ← hj, ← hj, hz]`. Simplify using `[hBA0]`. Establish `hdisj : LinearMap.range s ⊓ L₁.map j = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Take `⟨hx1, hx2⟩` from `Submodule.mem_inf.mp hx`. Take `⟨u, rfl⟩` from `LinearMap.mem_range.mp hx1`. Take `⟨z, hz, hzs⟩` from `Submodule.mem_map.mp hx2`.

Rewrite using `[Submodule.mem_bot]`. Establish `hz0 : z = 0`. Apply `hr₁inj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply `eq_zero_of_om` to reduce the goal to its premises.

Introduce `v`. Take `⟨z', rfl⟩` from `hr₁surj v`. Apply `hA` to reduce the goal to its premises. Rewrite using `[← hBz, ← hB, ← hj z, hzs, hjs, map_zero]`. Rewrite using `[← hzs, hz0, map_zero]`.

Set `L' : Submodule F V` to `LinearMap.range s ⊔ L₁.map j`. Establish `hfinL' : finrank F L' = Fintype.card κ`. Establish `h1` using `Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range s) (L₁.map j)`. Rewrite `h1` using `[hdisj, finrank_bot, add_zero, LinearMap.finrank_range_of_inj hs, ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective j hjinj L₁), hfinL₁]`. Rewrite using `[← hd]`.

Conclude with `h1`. Establish `T1 : ∀ u u', om F κ (r (s u)) (r (s u')) = 0` using `fun u u' => hA (by`. Rewrite using `[← hBx, hss, map_zero])`. Establish `T2 : ∀ z u, om F κ (r (j z)) (r (s u)) = 0` using `fun z u => hA (by`. Rewrite using `[← hBx, hj, hjs, map_zero])`.

Establish `T3 : ∀ u z, om F κ (r (s u)) (r (j z)) = 0` using `fun u z => om_refl _ _ (T2 z u)`. Establish `T4 : ∀ z z', z ∈ L₁ → z' ∈ L₁ → om F κ (r (j z)) (r (j z')) = 0` using `fun z z' hz hz' => hA (by`. Rewrite using `[← hBx, hj, hj, hB, hBz, om_apply, (hL₁ z).mp hz, (hL₁ z').mp hz']`. Use the proof step `simp)`. Establish `hiso : ∀ x ∈ L', ∀ y ∈ L', om F κ (r x) (r y) = 0`.

Introduce `x hx y hy`. Take `⟨p, hp, q, hq, rfl⟩` from `Submodule.mem_sup.mp hx`. Take `⟨p', hp', q', hq', rfl⟩` from `Submodule.mem_sup.mp hy`. Take `⟨u, rfl⟩` from `LinearMap.mem_range.mp hp`. Take `⟨u', rfl⟩` from `LinearMap.mem_range.mp hp'`.

Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.mp hq`. Take `⟨z', hz', rfl⟩` from `Submodule.mem_map.mp hq'`. Simplify using `only [map_add, LinearMap.add_apply, T1, T2, T3, T4 z z' hz hz', add_zero]`. Use `⟨L'.map r, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha b hb`.

Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.mp ha`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hb`. Establish `h0` using `hiso x hx y hy`. Rewrite `h0` using `[om_apply]`. Conclude with `sub_eq_zero.mp h0`.

Rewrite using `[← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective r hrinj L'), hfinL']`. Introduce `t w hw`. Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.mp hw`. Take `⟨p, hp, q, hq, rfl⟩` from `Submodule.mem_sup.mp hx`. Take `⟨u, rfl⟩` from `LinearMap.mem_range.mp hp`.

Take `⟨z₀, hz₀, rfl⟩` from `Submodule.mem_map.mp hq`. Use `⟨u, t • inc₁ z₀, ?_, fun ψ φ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hr₁' z₀, emb_apply]`. Use function extensionality and compare the values at `i`. Simplify using `[(hL₁ z₀).mp hz₀]`.

Establish `hsum : t • emb A κ (r (s u + j z₀)) = co.e (t • inc (s u)) + co.e (jA (t • inc₁ z₀))`. Rewrite using `[← hr', map_add, map_add, hj, smul_add, map_smul, map_smul, map_smul]`. Establish `hω : (co.e (t • inc (s u))).1 ⬝ᵥ (co.e (jA (t • inc₁ z₀))).2 - (co.e (jA (t • inc₁ z₀))).1 ⬝ᵥ (co.e (t • inc (s u))).2 = 0`. Establish `hf` using `co.form (jA (inc₁ z₀)) (inc (s u))`. Rewrite `hf` using `[hjs]`.

Rewrite using `[map_smul, map_smul, map_smul]`. Simplify using `only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]`. Take the linear combination `(t * t) * hf`. Simplify using `only [Darboux.rho]`. Rewrite using `[hsum, schr_add ψ _ _ hω φ]`.
-/
theorem exists_lag [Invertible (2 : A)] [FiniteDimensional F V₁] [FiniteDimensional F U]
    (hA : Function.Injective (algebraMap F A)) (co : Darboux BA κ) (inc : V →ₗ[F] VA) (hinc : Function.Injective inc)
    (hr : ∀ x, ∃ w, co.e (inc x) = emb (F := F) A κ w)
    (co₁ : Darboux BB κ₁) (inc₁ : V₁ →ₗ[F] VB) (hinc₁ : Function.Injective inc₁)
    (hr₁ : ∀ x, ∃ w, co₁.e (inc₁ x) = emb (F := F) A κ₁ w) (hd₁ : finrank F V₁ = 2 * Fintype.card κ₁)
    (j : V₁ →ₗ[F] V) (jA : VB →ₗ[A] VA) (hj : ∀ z, inc (j z) = jA (inc₁ z)) (hB : ∀ z z', BA (jA z) (jA z') = BB z z')
    (s : U →ₗ[F] V) (hs : Function.Injective s) (hss : ∀ u u', BA (inc (s u)) (inc (s u')) = 0)
    (hjs : ∀ z u, BA (jA z) (inc (s u)) = 0) (hd : finrank F U + Fintype.card κ₁ = Fintype.card κ) :
    ∃ L : Submodule F ((κ → F) × (κ → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧ finrank F L = Fintype.card κ ∧
      ∀ (t : A), ∀ w ∈ L, ∃ (u : U) (z : VB), (co₁.e z).1 = 0 ∧ ∀ (ψ : AddChar A ℂ) (φ : (κ → A) → ℂ),
        schr ψ (t • emb A κ w) φ = co.rho ψ (t • inc (s u)) (co.rho ψ (jA z) φ) := by
  classical
  obtain ⟨r, hr'⟩ := exists_coord hA co inc hr
  obtain ⟨r₁, hr₁'⟩ := exists_coord hA co₁ inc₁ hr₁
  have hBx : ∀ x y, BA (inc x) (inc y) = algebraMap F A (om F κ (r x) (r y)) := fun x y => by
    rw [co.form, hr', hr', emb_form]
  have hBz : ∀ z z', BB (inc₁ z) (inc₁ z') = algebraMap F A (om F κ₁ (r₁ z) (r₁ z')) := fun z z' => by
    rw [co₁.form, hr₁', hr₁', emb_form]
  have hBA0 : ∀ w, BA w 0 = 0 := fun w => by
    rw [co.form]
    simp
  have hrinj : Function.Injective r := by
    intro a b hab
    apply hinc
    apply co.e.injective
    rw [hr', hr', hab]
  have hr₁inj : Function.Injective r₁ := by
    intro a b hab
    apply hinc₁
    apply co₁.e.injective
    rw [hr₁', hr₁', hab]
  have hr₁surj : Function.Surjective r₁ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := r₁) ?_).mp hr₁inj
    rw [hd₁, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
    ring
  let L₁ : Submodule F V₁ := LinearMap.ker ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁)
  have hL₁ : ∀ z, z ∈ L₁ ↔ (r₁ z).1 = 0 := fun z => by
    simp [L₁]
  have hfinL₁ : finrank F L₁ = Fintype.card κ₁ := by
    have hsurj : Function.Surjective ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁) := fun v => by
      obtain ⟨x, hx⟩ := hr₁surj (v, 0)
      exact ⟨x, by simp [hx]⟩
    have hrn := LinearMap.finrank_range_add_finrank_ker ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, hd₁] at hrn
    have e : finrank F L₁ =
        finrank F (LinearMap.ker ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁)) := rfl
    omega
  have hjinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).mpr fun z hz => ?_
    apply hr₁inj
    rw [map_zero]
    apply eq_zero_of_om
    intro v
    obtain ⟨z', rfl⟩ := hr₁surj v
    apply hA
    rw [← hBz, ← hB, ← hj, ← hj, hz]
    simp [hBA0]
  have hdisj : LinearMap.range s ⊓ L₁.map j = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx1
    obtain ⟨z, hz, hzs⟩ := Submodule.mem_map.mp hx2
    rw [Submodule.mem_bot]
    have hz0 : z = 0 := by
      apply hr₁inj
      rw [map_zero]
      apply eq_zero_of_om
      intro v
      obtain ⟨z', rfl⟩ := hr₁surj v
      apply hA
      rw [← hBz, ← hB, ← hj z, hzs, hjs, map_zero]
    rw [← hzs, hz0, map_zero]
  let L' : Submodule F V := LinearMap.range s ⊔ L₁.map j
  have hfinL' : finrank F L' = Fintype.card κ := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range s) (L₁.map j)
    rw [hdisj, finrank_bot, add_zero, LinearMap.finrank_range_of_inj hs,
      ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective j hjinj L₁), hfinL₁] at h1
    rw [← hd]
    exact h1
  have T1 : ∀ u u', om F κ (r (s u)) (r (s u')) = 0 := fun u u' => hA (by
    rw [← hBx, hss, map_zero])
  have T2 : ∀ z u, om F κ (r (j z)) (r (s u)) = 0 := fun z u => hA (by
    rw [← hBx, hj, hjs, map_zero])
  have T3 : ∀ u z, om F κ (r (s u)) (r (j z)) = 0 := fun u z => om_refl _ _ (T2 z u)
  have T4 : ∀ z z', z ∈ L₁ → z' ∈ L₁ → om F κ (r (j z)) (r (j z')) = 0 := fun z z' hz hz' => hA (by
    rw [← hBx, hj, hj, hB, hBz, om_apply, (hL₁ z).mp hz, (hL₁ z').mp hz']
    simp)
  have hiso : ∀ x ∈ L', ∀ y ∈ L', om F κ (r x) (r y) = 0 := by
    intro x hx y hy
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨p', hp', q', hq', rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hp
    obtain ⟨u', rfl⟩ := LinearMap.mem_range.mp hp'
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hq
    obtain ⟨z', hz', rfl⟩ := Submodule.mem_map.mp hq'
    simp only [map_add, LinearMap.add_apply, T1, T2, T3, T4 z z' hz hz', add_zero]
  refine ⟨L'.map r, ?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hb
    have h0 := hiso x hx y hy
    rw [om_apply] at h0
    exact sub_eq_zero.mp h0
  · rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective r hrinj L'), hfinL']
  · intro t w hw
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hw
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hp
    obtain ⟨z₀, hz₀, rfl⟩ := Submodule.mem_map.mp hq
    refine ⟨u, t • inc₁ z₀, ?_, fun ψ φ => ?_⟩
    · rw [map_smul, hr₁' z₀, emb_apply]
      funext i
      simp [(hL₁ z₀).mp hz₀]
    · have hsum : t • emb A κ (r (s u + j z₀)) = co.e (t • inc (s u)) + co.e (jA (t • inc₁ z₀)) := by
        rw [← hr', map_add, map_add, hj, smul_add, map_smul, map_smul, map_smul]
      have hω : (co.e (t • inc (s u))).1 ⬝ᵥ (co.e (jA (t • inc₁ z₀))).2 -
          (co.e (jA (t • inc₁ z₀))).1 ⬝ᵥ (co.e (t • inc (s u))).2 = 0 := by
        have hf := co.form (jA (inc₁ z₀)) (inc (s u))
        rw [hjs] at hf
        rw [map_smul, map_smul, map_smul]
        simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        linear_combination (t * t) * hf
      simp only [Darboux.rho]
      rw [hsum, schr_add ψ _ _ hω φ]

end Abs

section Mat

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β α' β' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype α'] [DecidableEq α']
  [Fintype β'] [DecidableEq β']

/- English proof (translation)
Simplify using `only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem hTens_eq (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = Matrix.trace (xᵀ * (JA * y.map c * JBᵀ)) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Rewrite using `[hTens_eq, hTens_eq]`. Establish `hm : (a * y * bᵀ).map c = a.map c * y.map c * (b.map c)ᵀ`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, map_sum, map_mul]`. Rewrite using `[hm]`.

Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`. Rewrite using `[Matrix.trace_mul_comm b]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem hTens_mul (JA : Matrix α α E) (JB : Matrix β β E) (a : Matrix α α' E) (b : Matrix β β' E) (x y : Matrix α' β' E) :
    hTens c JA JB (a * x * bᵀ) (a * y * bᵀ) = hTens c (aᵀ * JA * a.map c) (bᵀ * JB * b.map c) x y := by
  rw [hTens_eq, hTens_eq]
  have hm : (a * y * bᵀ).map c = a.map c * y.map c * (b.map c)ᵀ := by
    ext i j
    simp [Matrix.mul_apply, map_sum, map_mul]
  rw [hm]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm b]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [hTens, vecMulVec_apply, map_mul, dotProduct, Matrix.mulVec]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul_sum, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_vec (JA : Matrix α α E) (JB : Matrix β β E) (w : Matrix α β E) (a : α → E) (b : β → E) :
    hTens c JA JB w (vecMulVec a b) = (JA *ᵥ fun i => c (a i)) ⬝ᵥ (w *ᵥ (JB *ᵥ fun i => c (b i))) := by
  simp only [hTens, vecMulVec_apply, map_mul, dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end Mat

end PositivityTheory.ThKF0.Geo
