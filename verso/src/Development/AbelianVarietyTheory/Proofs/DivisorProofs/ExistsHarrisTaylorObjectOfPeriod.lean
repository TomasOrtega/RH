import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianVarietyOfHalvedPeriodMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormTwoSmulAndKerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointIffBiextensionPullbacksIsomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleKernelKilledOfComplexPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionOfComplexExpIntertwinesActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPTateSimilitudeComplexTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPoincareKernelComplexStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Build

/- English proof (translation)
Establish `h0 : e 0 = 1`. Use `hadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_mul.1 this |>.symm ▸ rfl`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simpa using h0`. Consider the case `succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]`.
-/
lemma exp_nsmul {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (hadd : ∀ z w, e (z + w) = e z * e w) (z : Fin g → ℂ) : ∀ n : ℕ, e (n • z) = e z ^ n := by
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this |>.symm ▸ rfl
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

/- English proof (translation)
Set `φ : La →ₗ[ℤ] ℤ` to `{ toFun := fun y => E₁ a y / k map_add' := fun u v => by`. Rewrite using `[map_add]`. Conclude with `Int.add_ediv_of_dvd_left (hdv u)`. Use the proof step `map_smul' := fun c u => by`. Rewrite using `[map_zsmul, smul_eq_mul, smul_eq_mul, RingHom.id_apply]`.

Conclude with `Int.mul_ediv_assoc c (hdv u) }`. Take `⟨x', hx''⟩` from `hperf φ`. Use `⟨x', ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Apply `nondeg` to reduce the goal to its premises.

Introduce `y`. Establish `hφ : E₁ x' y = e₀ * (E₁ a y / k)`. Use `congrArg (fun F : La →ₗ[ℤ] ℤ => F y) hx''` as an intermediate fact. Simplify `this` using `[φ]`. Establish `hm : (k : ℤ) * (E₁ a y / k) = E₁ a y` using `Int.mul_ediv_cancel' (hdv y)`.

Rewrite using `[hE₁]`. Simplify using `only [LinearMap.smul_apply, map_sub, map_nsmul, LinearMap.sub_apply, smul_eq_mul, nsmul_eq_mul, hφ]`. Take the linear combination `(-2 * (e₀:ℤ)) * hm`.
-/
lemma exists_nsmul_eq_of_dvd {La : Type} [AddCommGroup La] (EF E₁ : LinearMap.BilinForm ℤ La) (hE₁ : EF = (2:ℤ) • E₁)
    (e₀ : ℕ) (a : La) (k : ℕ) (hdv : ∀ y, (k : ℤ) ∣ E₁ a y) (nondeg : ∀ x, (∀ y, EF x y = 0) → x = 0)
    (hperf : ∀ f : La →ₗ[ℤ] ℤ, ∃ x, E₁ x = e₀ • f) : ∃ x', e₀ • a = k • x' := by
  let φ : La →ₗ[ℤ] ℤ :=
    { toFun := fun y => E₁ a y / k
      map_add' := fun u v => by
        rw [map_add]; exact Int.add_ediv_of_dvd_left (hdv u)
      map_smul' := fun c u => by
        rw [map_zsmul, smul_eq_mul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hdv u) }
  obtain ⟨x', hx''⟩ := hperf φ
  refine ⟨x', ?_⟩
  rw [← sub_eq_zero]
  apply nondeg
  intro y
  have hφ : E₁ x' y = e₀ * (E₁ a y / k) := by
    have := congrArg (fun F : La →ₗ[ℤ] ℤ => F y) hx''
    simpa [φ] using this
  have hm : (k : ℤ) * (E₁ a y / k) = E₁ a y := Int.mul_ediv_cancel' (hdv y)
  rw [hE₁]
  simp only [LinearMap.smul_apply, map_sub, map_nsmul, LinearMap.sub_apply, smul_eq_mul, nsmul_eq_mul, hφ]
  linear_combination (-2 * (e₀:ℤ)) * hm

/- English proof (translation)
Use extensionality with `u v`. Establish `h2` using `congrArg (fun B : LinearMap.BilinForm ℤ La => B u v) h`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul] at h2`. Use linear arithmetic over natural numbers and integers.
-/
lemma half_unique {La : Type} [AddCommGroup La] (E E' : LinearMap.BilinForm ℤ La) (h : (2:ℤ) • E = (2:ℤ) • E') :
    E = E' := by
  ext u v
  have h2 := congrArg (fun B : LinearMap.BilinForm ℤ La => B u v) h
  simp only [LinearMap.smul_apply, smul_eq_mul] at h2
  omega

end GlobalTheory.UPel.HT.Build

open GlobalTheory.UPel.HT.Build in

/- English proof (translation)
Introduce `p _ D R _ b N σ ρ D' t Q hN hNp htype hcls hper`. Take `⟨hgen, E₁, hE₁, e₀, he₀p, hperf⟩` from `hcls`. Take `⟨A, _, _, act, P, e, hab, hdim, hP, r₁, r₂, hsy, ham, hexp, hker, hact, hweil⟩` from `GlobalTheory.T.exists_abelianVariety_of_halved_periodMap D.O D.inv D.g ρ D' Q E₁ hper hE₁`. Establish `hadd` using `hexp.1`. Establish `hsurj` using `hexp.2.1`.

Take `⟨hlie, hlieR⟩` from `GlobalTheory.T.lieCondition_of_complexExp_intertwines_action p D R b N σ ρ A act e hab hdim hexp hact htype`. Establish `hgen'` using `hgen`. Take `⟨f, ν, rfl, -, hf⟩` from `hgen`. Establish `hfN` using `hf N hN hNp`. Set `eta : D.La → (𝟙_ (Over (Sp ℂ)) ⟶ A)` to `fun a => e ((N : ℂ)⁻¹ • Q (f N a))`.

Establish `heta : ∀ a, toUnit _ ≫ eta a = e ((N : ℂ)⁻¹ • Q (f N a))` using `fun a => Category.id_comp _`. Establish `hsc : ∀ (c : D.O) (k : ℂ) (x : D'.La), e (k • Q (c • x)) = e (k • Q x) ≫ act.act c`. Introduce `c k x`. Rewrite using `[hper.1, ← Matrix.mulVec_smul, hact]`. Establish `hNz : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`.

Establish `hQ1 : ∀ x, e (Q x) = 1` using `fun x => (hker _).2 ⟨x, rfl⟩`. Establish `hgeom` using `GlobalTheory.T.exists_primeToP_tateSimilitude_complexTorus p D N ρ A act _ D' (f N) Q e eta hN hNp hab (pull_isLB hP _) hgen' hper hadd hsurj hker hact hweil heta`. Set `o : Obj b N (spMap σ)` to `{ A := A ab := hab act := act P := P isLB := hP rig₁ := r₁ rig₂ := r₂`. Use symmetry as in `:= hsy`. Use `ample := ham`.

Use `kerP := ⟨e₀, he₀p, GlobalTheory.T.birigidified_bundle_kernel_killed_of_complex_points A D.g hab hdim P hP r₁ r₂ hsy ham e₀ (fun x hx => by`. Take `⟨k, hk, hxk⟩` from `GlobalTheory.T.exists_pow_eq_one_of_poincareKernel_complex A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp hper.2.1 hper.2.2.2.1 hker hweil x hx`. Take `⟨z, rfl⟩` from `hsurj x`. Establish `hk' : (k : ℂ) ≠ 0` using `by exact_mod_cast hk.ne'`. Establish `h1 : e (k • z) = 1` using `by rw [exp_nsmul e hadd]; exact hxk`.

Take `⟨a, ha⟩` from `(hker _).1 h1`. Establish `hz : z = (k : ℂ)⁻¹ • Q a`. Rewrite using `[ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk', one_smul]`. Take `⟨E₁', hE₁', hdiv⟩` from `GlobalTheory.T.diag_form_two_smul_and_ker_alt A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp hper.2.1 hker hweil`. Establish `hx' : ∃ t : (P.pull (lift (snd A (Over.mk (𝟙 (Sp ℂ))) ≫ e ((k : ℂ)⁻¹ • Q a)) (fst A (Over.mk (𝟙 (Sp ℂ))))).left).Gen, t.IsGen`.

Rewrite using `[← hz]`. Conclude with `hx`. Establish `hdv : ∀ y, (k : ℤ) ∣ E₁' a y` using `(hdiv k a hk).2 hx'`. Establish `hEE : E₁' = E₁` using `half_unique _ _ (hE₁'.symm.trans hE₁)`. Rewrite `hdv` using `[hEE]`.

Take `⟨x', key⟩` from `exists_nsmul_eq_of_dvd D'.EF E₁ hE₁ e₀ a k hdv D'.nondeg hperf`. Establish `hQ : Q x' = e₀ • ((k : ℂ)⁻¹ • Q a)`. Rewrite using `[smul_comm, ← map_nsmul, key, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk', one_smul]`. Use `show e z ^ e₀ = 1`. Rewrite using `[← exp_nsmul e hadd, hz, ← hQ]`.

Conclude with `hQ1 x')⟩`. Use `rosati := fun c => by`. Use `(GlobalTheory.T.rosati_adjoint_iff_biextension_pullbacks_isomorphic A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp hper.2.1 hker hweil (act.act c) (act.act (D.star c).unop) (AddMonoidHom.mk' (fun x => c • x) (smul_add c)) (AddMonoidHom.mk' (fun x => (D.star c).unop • x) ( …` and prove the remaining obligations. Introduce `x y`. Conclude with `D'.adj c x y`.

Use `lie := hlie`. Use `lieRank := fun k _ _ x β hx i => hlieR k x β hx i`. Use `eta := eta`. Use `eta_add := fun x y => by show e _ = e _ * e _ erw [map_add (f N) x y, map_add, smul_add, hadd]`. Both sides reduce to the same expression.

Use `eta_lin := fun c x => by`. Take `⟨e', he'⟩` from `hfN.2.1 c x`. Use `show e _ = e _ ≫ _`. Use `erw [he', map_add, smul_add, hadd, hsc, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hNz, one_smul, hQ1, _root_.mul_one]`. Use `eta_ker := fun x => by show e _ = 1 erw [map_nsmul (f N) N x, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hNz, one_smul, hQ1]`.

Use `geom := fun k _ _ x β _ => hgeom k x }`. Use `⟨o, hdim, pull_isLB hP _, e, ?_⟩` and prove the remaining obligations. Use `⟨Category.id_comp _, hper, hexp, hker, hact, hweil, heta⟩` and prove the remaining obligations.
-/
theorem GlobalTheory.UPel.HT.exists_obj_unifAt_of_period : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) t Q, 0 < N → N.Coprime p → b.IsType σ ρ → D.Cls N D' t → IsPeriod D' ρ Q → ∃ (o : Obj b N (spMap σ)) (h : _) (hL : _) (e : _), UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  intro p _ D R _ b N σ ρ D' t Q hN hNp htype hcls hper
  obtain ⟨hgen, E₁, hE₁, e₀, he₀p, hperf⟩ := hcls
  obtain ⟨A, _, _, act, P, e, hab, hdim, hP, r₁, r₂, hsy, ham, hexp, hker, hact, hweil⟩ :=
    GlobalTheory.T.exists_abelianVariety_of_halved_periodMap D.O D.inv D.g ρ D' Q E₁ hper hE₁
  have hadd := hexp.1
  have hsurj := hexp.2.1
  obtain ⟨hlie, hlieR⟩ := GlobalTheory.T.lieCondition_of_complexExp_intertwines_action p D R b N σ ρ A act e hab hdim hexp hact htype
  have hgen' := hgen
  obtain ⟨f, ν, rfl, -, hf⟩ := hgen
  have hfN := hf N hN hNp
  let eta : D.La → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun a => e ((N : ℂ)⁻¹ • Q (f N a))
  have heta : ∀ a, toUnit _ ≫ eta a = e ((N : ℂ)⁻¹ • Q (f N a)) := fun a => Category.id_comp _
  have hsc : ∀ (c : D.O) (k : ℂ) (x : D'.La), e (k • Q (c • x)) = e (k • Q x) ≫ act.act c := by
    intro c k x
    rw [hper.1, ← Matrix.mulVec_smul, hact]
  have hNz : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hQ1 : ∀ x, e (Q x) = 1 := fun x => (hker _).2 ⟨x, rfl⟩
  have hgeom := GlobalTheory.T.exists_primeToP_tateSimilitude_complexTorus p D N ρ A act _ D' (f N) Q e eta hN hNp hab (pull_isLB hP _) hgen' hper hadd hsurj hker
    hact hweil heta
  let o : Obj b N (spMap σ) :=
    { A := A
      ab := hab
      act := act
      P := P
      isLB := hP
      rig₁ := r₁
      rig₂ := r₂
      symm := hsy
      ample := ham
      kerP := ⟨e₀, he₀p, GlobalTheory.T.birigidified_bundle_kernel_killed_of_complex_points A D.g hab hdim P hP r₁ r₂ hsy ham e₀ (fun x hx => by
        obtain ⟨k, hk, hxk⟩ := GlobalTheory.T.exists_pow_eq_one_of_poincareKernel_complex A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp hper.2.1
          hper.2.2.2.1 hker hweil x hx
        obtain ⟨z, rfl⟩ := hsurj x
        have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
        have h1 : e (k • z) = 1 := by rw [exp_nsmul e hadd]; exact hxk
        obtain ⟨a, ha⟩ := (hker _).1 h1
        have hz : z = (k : ℂ)⁻¹ • Q a := by
          rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk', one_smul]
        obtain ⟨E₁', hE₁', hdiv⟩ := GlobalTheory.T.diag_form_two_smul_and_ker_alt A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp
          hper.2.1 hker hweil
        have hx' : ∃ t : (P.pull (lift (snd A (Over.mk (𝟙 (Sp ℂ))) ≫ e ((k : ℂ)⁻¹ • Q a))
            (fst A (Over.mk (𝟙 (Sp ℂ))))).left).Gen, t.IsGen := by
          rw [← hz]; exact hx
        have hdv : ∀ y, (k : ℤ) ∣ E₁' a y := (hdiv k a hk).2 hx'
        have hEE : E₁' = E₁ := half_unique _ _ (hE₁'.symm.trans hE₁)
        rw [hEE] at hdv
        obtain ⟨x', key⟩ := exists_nsmul_eq_of_dvd D'.EF E₁ hE₁ e₀ a k hdv D'.nondeg hperf
        have hQ : Q x' = e₀ • ((k : ℂ)⁻¹ • Q a) := by
          rw [smul_comm, ← map_nsmul, key, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk',
            one_smul]
        show e z ^ e₀ = 1
        rw [← exp_nsmul e hadd, hz, ← hQ]
        exact hQ1 x')⟩
      rosati := fun c => by
        refine (GlobalTheory.T.rosati_adjoint_iff_biextension_pullbacks_isomorphic A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp hper.2.1 hker hweil
          (act.act c) (act.act (D.star c).unop) (AddMonoidHom.mk' (fun x => c • x) (smul_add c))
          (AddMonoidHom.mk' (fun x => (D.star c).unop • x) (smul_add _)) (act.hom c) (act.hom _)
          (fun k x _ => hsc c _ x) (fun k x _ => hsc _ _ x)).2 ?_
        intro x y
        exact D'.adj c x y
      lie := hlie
      lieRank := fun k _ _ x β hx i => hlieR k x β hx i
      eta := eta
      eta_add := fun x y => by
        show e _ = e _ * e _
        erw [map_add (f N) x y, map_add, smul_add, hadd]
        rfl
      eta_lin := fun c x => by
        obtain ⟨e', he'⟩ := hfN.2.1 c x
        show e _ = e _ ≫ _
        erw [he', map_add, smul_add, hadd, hsc, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hNz, one_smul, hQ1, _root_.mul_one]
      eta_ker := fun x => by
        show e _ = 1
        erw [map_nsmul (f N) N x, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hNz, one_smul, hQ1]
      geom := fun k _ _ x β _ => hgeom k x }
  refine ⟨o, hdim, pull_isLB hP _, e, ?_⟩
  refine ⟨Category.id_comp _, hper, hexp, hker, hact, hweil, heta⟩
