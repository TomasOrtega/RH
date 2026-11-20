import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)

namespace GlobalTheory.ImgVB

/- English proof (translation)
Use `set B := A.submatrix id J with hB`. Establish `hc : ∀ k, B.det ∣ B.cramer (fun i => A i j) k`. Introduce `k`. Rewrite using `[Matrix.cramer_apply]`. Establish `: B.updateCol k (fun i => A i j) = A.submatrix id (Function.update J k j)`.

Use extensionality with `i l`. Distinguish the cases in `hl : l = k`. Substitute `hl` using the available equality. Simplify using `[B, Matrix.updateCol_self]`. Simplify using `[B, Matrix.updateCol_ne hl, Function.update_of_ne hl]`.

Rewrite using `[this]`. Conclude with `hdiv _`. Use `choose c hc using hc`. Use `⟨c, fun i => ?_⟩` and prove the remaining obligations. Establish `h1` using `Matrix.mulVec_cramer B (fun i => A i j)`.

Establish `h2 : B.cramer (fun i => A i j) = B.det • c` using `funext fun k => by simp [hc k]`. Rewrite `h1` using `[h2, Matrix.mulVec_smul]`. Establish `h3` using `congrFun h1 i`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at h3`. Establish `h4` using `mul_left_cancel₀ hd h3`.

Rewrite using `[← h4, Matrix.mulVec, dotProduct]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.
-/
theorem exists_col_comb {R : Type} [CommRing R] [IsDomain R] {r m : ℕ}
    (A : Matrix (Fin r) (Fin m) R) (J : Fin r → Fin m) (hd : (A.submatrix id J).det ≠ 0)
    (hdiv : ∀ K : Fin r → Fin m, (A.submatrix id J).det ∣ (A.submatrix id K).det) (j : Fin m) :
    ∃ c : Fin r → R, ∀ i, A i j = ∑ k, c k * A i (J k) := by
  classical
  set B := A.submatrix id J with hB
  have hc : ∀ k, B.det ∣ B.cramer (fun i => A i j) k := by
    intro k
    rw [Matrix.cramer_apply]
    have : B.updateCol k (fun i => A i j) = A.submatrix id (Function.update J k j) := by
      ext i l
      by_cases hl : l = k
      · subst hl; simp [B, Matrix.updateCol_self]
      · simp [B, Matrix.updateCol_ne hl, Function.update_of_ne hl]
    rw [this]; exact hdiv _
  choose c hc using hc
  refine ⟨c, fun i => ?_⟩
  have h1 := Matrix.mulVec_cramer B (fun i => A i j)
  have h2 : B.cramer (fun i => A i j) = B.det • c := funext fun k => by simp [hc k]
  rw [h2, Matrix.mulVec_smul] at h1
  have h3 := congrFun h1 i
  simp only [Pi.smul_apply, smul_eq_mul] at h3
  have h4 := mul_left_cancel₀ hd h3
  rw [← h4, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/- English proof (translation)
The claim follows from `Matrix.eq_zero_of_mulVec_eq_zero hd (funext fun i => by simpa [Matrix.mulVec, dotProduct, mul_comm] using hx i)`.
-/
theorem eq_zero_of_comb {R : Type} [CommRing R] [IsDomain R] {r m : ℕ}
    (A : Matrix (Fin r) (Fin m) R) (J : Fin r → Fin m) (hd : (A.submatrix id J).det ≠ 0)
    (x : Fin r → R) (hx : ∀ i, ∑ k, x k * A i (J k) = 0) : x = 0 :=
  Matrix.eq_zero_of_mulVec_eq_zero hd (funext fun i => by
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hx i)

end GlobalTheory.ImgVB

namespace GlobalTheory.ImgVB

/- English proof (translation)
Use `fun V h => ⟨inj V h, fun s => ?_⟩` and prove the remaining obligations. Use `choose W hW hx a ha using fun x : V => loc V h s x x.2`. Establish `hc : V ≤ iSup W` using `fun x hxV => Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩`. Establish `key (x y : V) : (fun i => resG Y (inf_le_left : W x ⊓ W y ≤ W x) (a x i)) = fun i => resG Y (inf_le_right : W x ⊓ W y ≤ W y) (a y i)`. Apply `inj _ (inf_le_left.trans ((hW x).trans h))` to reduce the goal to its premises.

Rewrite using `[← GlobalTheory.VB.resM_linearCombination e ((hW x).trans h), ← GlobalTheory.VB.resM_linearCombination e ((hW y).trans h), ha, ha, resM_resM, resM_resM]`. Use `choose b hb' using fun i => exists_fun_of_cover W hW hc (fun x => a x i) fun x y => congrFun (key x y) i`. Use `⟨b, sec_ext_of_cover W hW hc fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.VB.resM_linearCombination, ← ha x]`. Conclude with `congrArg _ (funext fun i => hb' i x)`.
-/
theorem isFrame_of_inj_of_local {Y : Scheme.{0}} {M : Y.Modules} {ι : Type} [Fintype ι]
    {U : Y.Opens} {e : ι → Γ(M, U)}
    (inj : ∀ (W : Y.Opens) (h : W ≤ U),
      Function.Injective (Fintype.linearCombination Γ(Y, W) fun i => resM M h (e i)))
    (loc : ∀ (W : Y.Opens) (h : W ≤ U) (s : Γ(M, W)) (x : Y), x ∈ W →
      ∃ (W' : Y.Opens) (h' : W' ≤ W), x ∈ W' ∧ ∃ a : ι → Γ(Y, W'),
        Fintype.linearCombination Γ(Y, W') (fun i => resM M (h'.trans h) (e i)) a = resM M h' s) :
    GlobalTheory.VB.IsFrame e := by
  refine fun V h => ⟨inj V h, fun s => ?_⟩
  choose W hW hx a ha using fun x : V => loc V h s x x.2
  have hc : V ≤ iSup W := fun x hxV => Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩
  have key (x y : V) : (fun i => resG Y (inf_le_left : W x ⊓ W y ≤ W x) (a x i)) =
      fun i => resG Y (inf_le_right : W x ⊓ W y ≤ W y) (a y i) := by
    apply inj _ (inf_le_left.trans ((hW x).trans h))
    rw [← GlobalTheory.VB.resM_linearCombination e ((hW x).trans h),
      ← GlobalTheory.VB.resM_linearCombination e ((hW y).trans h), ha, ha, resM_resM, resM_resM]
  choose b hb' using fun i => exists_fun_of_cover W hW hc (fun x => a x i)
    fun x y => congrFun (key x y) i
  refine ⟨b, sec_ext_of_cover W hW hc fun x => ?_⟩
  rw [GlobalTheory.VB.resM_linearCombination, ← ha x]
  exact congrArg _ (funext fun i => hb' i x)

end GlobalTheory.ImgVB

namespace GlobalTheory.ImgVB

/- English proof (translation)
Introduce `y`. Take `⟨V, eF, eE, a, J, hy, hF, hE, hφ, hd, hdiv⟩` from `H y`. Use `haveI : Nonempty V := ⟨⟨y, hy⟩⟩`. Use `choose c hc using exists_col_comb a J hd hdiv`. Establish `hι : ∀ (W : Y.Opens) (s : Γ(F, W)), (image.ι φ).app W ((factorThruImage φ).app W s) = φ.app W s` using `fun W s => by`.

Rewrite using `[GlobalTheory.QCoh.app_app, image.fac]`. Establish `hinj : ∀ W : Y.Opens, Function.Injective ((image.ι φ).app W)` using `fun W => GlobalTheory.QCoh.app_injective_of_mono _ W`. Set `t : Fin r → Γ(Limits.image φ, V)` to `fun k => (factorThruImage φ).app V (eF (J k))`. Establish `hιt : ∀ (W : Y.Opens) (h : W ≤ V) (k : Fin r), (image.ι φ).app W (resM _ h (t k)) = ∑ i, resG Y h (a i (J k)) • resM E h (eE i)`. Introduce `W h k`.

Rewrite using `[app_resM, hι, hφ, map_sum]`. Simplify using `only [resM_smul]`. Establish `hpt : ∀ j, (factorThruImage φ).app V (eF j) = ∑ k, c j k • t k`. Introduce `j`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[hι, hφ, map_sum]`. Simplify using `only [Scheme.Modules.Hom.app_smul, t, hι, hφ, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul, hc j i]`.

Use `⟨V, t, hy, isFrame_of_inj_of_local (fun W h => ?_) (fun W h s x hx => ?_)⟩` and prove the remaining obligations. Use `(injective_iff_map_eq_zero _).2 fun x hx => ?_` and prove the remaining obligations. Establish `h1` using `congrArg ((image.ι φ).app W) hx`. Rewrite `h1` using `[map_zero, Fintype.linearCombination_apply, map_sum]`. Simplify using `only [Scheme.Modules.Hom.app_smul, hιt, Finset.smul_sum, smul_smul] at h1`.

Rewrite `h1` using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul] at h1`. Establish `h2` using `(hE W h).1 (a₁ := fun i => ∑ k, x k * resG Y h (a i (J k))) (a₂ := 0) (by rw [Fintype.linearCombination_apply, h1, map_zero])`. Use function extensionality and compare the values at `k`. Use `fun_ext_of_cover (fun _ : W => W) (fun _ => le_rfl) (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hz⟩) fun p => ?_` and prove the remaining obligations.

Use `haveI : Nonempty W := ⟨p⟩`. Rewrite using `[resG_self, resG_self]`. Establish `hd' : ((a.map (resG Y h)).submatrix id J).det ≠ 0`. Rewrite using `[Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `fun h0 => hd (map_injective_of_isIntegral Y (homOfLE h) (h0.trans (map_zero _).symm))`.

Use `eq_zero_of_comb (a.map (resG Y h)) J hd' x fun i => by` as an intermediate fact. Simplify using `using congrFun h2 i`. Conclude with `congrFun this k`. Take `⟨W', h', hxW', f, hf⟩` from `GlobalTheory.VB.exists_app_eq_of_epi (factorThruImage φ) s hx`. Take `⟨b, rfl⟩` from `(hF W' (h'.trans h)).2 f`.

Use `⟨W', h', hxW', fun k => ∑ j, b j * resG Y (h'.trans h) (c j k), ?_⟩` and prove the remaining obligations. Rewrite using `[← hf, Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]`. Simplify using `only [Scheme.Modules.Hom.app_smul, app_resM, hpt, map_sum, resM_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem isVB_image_of_minor (Y : Scheme.{0}) [IsIntegral Y] (F E : Y.Modules) (φ : F ⟶ E)
    (r m : ℕ)
    (H : ∀ y : Y, ∃ (V : Y.Opens) (eF : Fin m → Γ(F, V)) (eE : Fin r → Γ(E, V))
      (a : Matrix (Fin r) (Fin m) Γ(Y, V)) (J : Fin r → Fin m), y ∈ V ∧ GlobalTheory.VB.IsFrame eF ∧
      GlobalTheory.VB.IsFrame eE ∧ (∀ j, φ.app V (eF j) = ∑ k, a k j • eE k) ∧
      (a.submatrix id J).det ≠ 0 ∧
      ∀ K : Fin r → Fin m, (a.submatrix id J).det ∣ (a.submatrix id K).det) :
    GlobalTheory.VB.IsVB (Limits.image φ) r := by
  intro y
  obtain ⟨V, eF, eE, a, J, hy, hF, hE, hφ, hd, hdiv⟩ := H y
  haveI : Nonempty V := ⟨⟨y, hy⟩⟩
  choose c hc using exists_col_comb a J hd hdiv
  have hι : ∀ (W : Y.Opens) (s : Γ(F, W)),
      (image.ι φ).app W ((factorThruImage φ).app W s) = φ.app W s := fun W s => by
    rw [GlobalTheory.QCoh.app_app, image.fac]
  have hinj : ∀ W : Y.Opens, Function.Injective ((image.ι φ).app W) :=
    fun W => GlobalTheory.QCoh.app_injective_of_mono _ W
  let t : Fin r → Γ(Limits.image φ, V) := fun k => (factorThruImage φ).app V (eF (J k))
  have hιt : ∀ (W : Y.Opens) (h : W ≤ V) (k : Fin r),
      (image.ι φ).app W (resM _ h (t k)) = ∑ i, resG Y h (a i (J k)) • resM E h (eE i) := by
    intro W h k
    rw [app_resM, hι, hφ, map_sum]
    simp only [resM_smul]
  have hpt : ∀ j, (factorThruImage φ).app V (eF j) = ∑ k, c j k • t k := by
    intro j
    apply hinj
    rw [hι, hφ, map_sum]
    simp only [Scheme.Modules.Hom.app_smul, t, hι, hφ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul, hc j i]
  refine ⟨V, t, hy, isFrame_of_inj_of_local (fun W h => ?_) (fun W h s x hx => ?_)⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have h1 := congrArg ((image.ι φ).app W) hx
    rw [map_zero, Fintype.linearCombination_apply, map_sum] at h1
    simp only [Scheme.Modules.Hom.app_smul, hιt, Finset.smul_sum, smul_smul] at h1
    rw [Finset.sum_comm] at h1
    simp only [← Finset.sum_smul] at h1
    have h2 := (hE W h).1 (a₁ := fun i => ∑ k, x k * resG Y h (a i (J k))) (a₂ := 0)
      (by rw [Fintype.linearCombination_apply, h1, map_zero])
    funext k
    refine fun_ext_of_cover (fun _ : W => W) (fun _ => le_rfl)
      (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hz⟩) fun p => ?_
    haveI : Nonempty W := ⟨p⟩
    rw [resG_self, resG_self]
    have hd' : ((a.map (resG Y h)).submatrix id J).det ≠ 0 := by
      rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact fun h0 => hd (map_injective_of_isIntegral Y (homOfLE h) (h0.trans (map_zero _).symm))
    have := eq_zero_of_comb (a.map (resG Y h)) J hd' x fun i => by
      simpa using congrFun h2 i
    exact congrFun this k
  · obtain ⟨W', h', hxW', f, hf⟩ := GlobalTheory.VB.exists_app_eq_of_epi (factorThruImage φ) s hx
    obtain ⟨b, rfl⟩ := (hF W' (h'.trans h)).2 f
    refine ⟨W', h', hxW', fun k => ∑ j, b j * resG Y (h'.trans h) (c j k), ?_⟩
    rw [← hf, Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
    simp only [Scheme.Modules.Hom.app_smul, app_resM, hpt, map_sum, resM_smul, Finset.smul_sum,
      smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]

end GlobalTheory.ImgVB
