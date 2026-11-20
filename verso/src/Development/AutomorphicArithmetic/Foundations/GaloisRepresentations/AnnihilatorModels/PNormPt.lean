import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `hSN hBOC hSec hEA hGen hPtC l f n hl O _ _ _ ϖ hϖ hl0 hlu Y g hg T hPt U V hU hV h`. Introduce `B _ _ hlB I _ z hs B' _ ρ hρπ ι _ x`. Use `set q := l ^ f with hq`. Use `set πU := Y.presheaf.map (homOfLE le_top).op (fn g ϖ) with hπU`. Use `letI : ∀ j, Algebra Γ(Y, U) Γ((T j).Z, (T j).p ⁻¹ᵁ U) := fun j => (T j).alg U`.

Take `⟨hBase, m, hm⟩` from `hBOC l O ϖ hϖ hl0 hlu Y g hg U hU`. Set `s : (j : Fin (n + 1)) → ι → Γ((T j).Z, (T j).p ⁻¹ᵁ U)` to `fun j k => ((T j).r.appLE V ((T j).p ⁻¹ᵁ U) (h j)).hom (x k) ^ (q ^ (n - (j : ℕ)))`. Establish `hρ : ∀ a ∈ Ideal.span {πU}, ρ (algebraMap Γ(Y, U) B a) = 0`. Introduce `a ha`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`.

Rewrite using `[map_mul, map_mul, hρπ, mul_zero]`. Establish `key` using `hSN l Γ(Y, U) (Ideal.span {πU}) hBase (Fin (n + 1)) (fun j => Γ((T j).Z, (T j).p ⁻¹ᵁ U)) (fun j => (T j).d) (fun j => hEA l Y (T j) U hU) (wEv q) (wOd q) ι s ?_ B hlB I z hs B' ρ hρ`. Simplify `key` using `only [s, map_pow]`. Introduce `W _ _ _ _ _ hlW hmin J _ zz hbij`. Establish `hgen` using `hGen Y (fn g ϖ) U hU W (algebraMap Γ(Y, U) W) hmin`.

Establish `hlm : (l : W) ∈ IsLocalRing.maximalIdeal W`. Establish `h1 : ((l : Γ(Y, U)) ^ m) ∈ Ideal.comap (algebraMap Γ(Y, U) W) (IsLocalRing.maximalIdeal W)` using `hmin.1.2 hm`. Rewrite `h1` using `[Ideal.mem_comap, map_pow, map_natCast]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal W).isPrime.mem_of_pow_mem m h1`. Establish `hlκ : ((l : IsLocalRing.ResidueField W)) = 0`.

Rewrite using `[← map_natCast (IsLocalRing.residue W), IsLocalRing.residue_eq_zero_iff]`. Conclude with `hlm`. Use `haveI : Fact l.Prime := ⟨hl⟩`. Use `haveI : CharP (IsLocalRing.ResidueField W) l := (CharP.charP_iff_prime_eq_zero hl).mpr hlκ`. Set `φ` to `iterateFrobenius (IsLocalRing.ResidueField W) l f`.

Establish `hφ : ∀ a, φ a = a ^ q` using `fun a => rfl`. Establish `hφm : ∀ (k : ℕ) a, (φ ^ k) a = a ^ (q ^ k)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro a`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `a`. Rewrite using `[pow_succ, RingHom.mul_def, RingHom.comp_apply, ih, hφ, ← pow_mul, pow_succ']`. Use `choose hZ hE using fun j => hSec l Y (T j) U hU`.

Use `choose e he using fun j => hE j W`. Establish `hbij' : ∀ j, Function.Bijective (fun i => e j (zz j i))` using `fun j => (e j).bijective.comp (hbij j)`. Establish `alt` using `hPt W hlW (ptOf hU W (algebraMap Γ(Y, U) W)) hgen φ hφ J (fun j i => e j (zz j i)) hbij'`. Unfold `AltId at alt`. Establish `hterm : ∀ (j : Fin (n + 1)) (i : J j), (twist φ Y)^[n - (j : ℕ)] (resPt W ≫ (e j (zz j i)).1 ≫ (T j).r) = ptOf hV (IsLocalRing.ResidueField W) ((φ ^ (n - (j : ℕ))).comp ((IsLocalRing.residue W).comp ((zz j i).toRingHom.comp ((T j).r.appLE V ((T j).p ⁻¹ᵁ U) (h j)).hom)))`.

Introduce `j i`. Rewrite using `[he j (zz j i)]`. Unfold `resPt`. Rewrite using `[(hPtC Y V hV (IsLocalRing.ResidueField W)).2.2 (T j).Z (T j).r ((T j).p ⁻¹ᵁ U) (hZ j) (h j) W (IsLocalRing.residue W) (zz j i).toRingHom]`. Rewrite using `[(hPtC Y V hV (IsLocalRing.ResidueField W)).2.1]`.

Simplify using `only [hterm] at alt`. Set `G : (Spec (CommRingCat.of (IsLocalRing.ResidueField W)) ⟶ Y) → ι → IsLocalRing.ResidueField W` to `fun P k => if hP : ∃ F, ptOf hV (IsLocalRing.ResidueField W) F = P then (Classical.choose hP) (x k) else 0`. Establish `hG : ∀ F, G (ptOf hV (IsLocalRing.ResidueField W) F) = fun k => F (x k)`. Introduce `F`. Use function extensionality and compare the values at `k`.

Establish `hP : ∃ F', ptOf hV (IsLocalRing.ResidueField W) F' = ptOf hV (IsLocalRing.ResidueField W) F` using `⟨F, rfl⟩`. Simplify using `only [G, dif_pos hP]`. Rewrite using `[(hPtC Y V hV (IsLocalRing.ResidueField W)).1 (Classical.choose_spec hP)]`. Establish `alt2` using `congrArg (Multiset.map G) alt`. Rewrite `alt2` using `[pts_map, pts_map]`.

Simplify using `only [hG, RingHom.comp_apply, hφm, AlgHom.coe_toRingHom] at alt2`. Simplify using `only [s, map_pow]`. Conclude with `alt2`.
-/
theorem UpperTheory.Gal.crystallineComparison.normPt_of :
    SameNormRing → BaseOfChart → SecChart → EtAwayChart → GenChart → PtChart → NormOfPt := by
  intro hSN hBOC hSec hEA hGen hPtC l f n hl O _ _ _ ϖ hϖ hl0 hlu Y g hg T hPt U V hU hV h
  intro B _ _ hlB I _ z hs B' _ ρ hρπ ι _ x
  set q := l ^ f with hq
  set πU := Y.presheaf.map (homOfLE le_top).op (fn g ϖ) with hπU
  letI : ∀ j, Algebra Γ(Y, U) Γ((T j).Z, (T j).p ⁻¹ᵁ U) := fun j => (T j).alg U
  obtain ⟨hBase, m, hm⟩ := hBOC l O ϖ hϖ hl0 hlu Y g hg U hU
  let s : (j : Fin (n + 1)) → ι → Γ((T j).Z, (T j).p ⁻¹ᵁ U) := fun j k =>
    ((T j).r.appLE V ((T j).p ⁻¹ᵁ U) (h j)).hom (x k) ^ (q ^ (n - (j : ℕ)))
  have hρ : ∀ a ∈ Ideal.span {πU}, ρ (algebraMap Γ(Y, U) B a) = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_mul, hρπ, mul_zero]
  have key := hSN l Γ(Y, U) (Ideal.span {πU}) hBase (Fin (n + 1))
    (fun j => Γ((T j).Z, (T j).p ⁻¹ᵁ U)) (fun j => (T j).d) (fun j => hEA l Y (T j) U hU)
    (wEv q) (wOd q) ι s ?_ B hlB I z hs B' ρ hρ
  · simpa only [s, map_pow] using key
  intro W _ _ _ _ _ hlW hmin J _ zz hbij
  have hgen := hGen Y (fn g ϖ) U hU W (algebraMap Γ(Y, U) W) hmin
  have hlm : (l : W) ∈ IsLocalRing.maximalIdeal W := by
    have h1 : ((l : Γ(Y, U)) ^ m) ∈ Ideal.comap (algebraMap Γ(Y, U) W) (IsLocalRing.maximalIdeal W) :=
      hmin.1.2 hm
    rw [Ideal.mem_comap, map_pow, map_natCast] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal W).isPrime.mem_of_pow_mem m h1
  have hlκ : ((l : IsLocalRing.ResidueField W)) = 0 := by
    rw [← map_natCast (IsLocalRing.residue W), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : CharP (IsLocalRing.ResidueField W) l := (CharP.charP_iff_prime_eq_zero hl).mpr hlκ
  let φ := iterateFrobenius (IsLocalRing.ResidueField W) l f
  have hφ : ∀ a, φ a = a ^ q := fun a => rfl
  have hφm : ∀ (k : ℕ) a, (φ ^ k) a = a ^ (q ^ k) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, ih, hφ, ← pow_mul, pow_succ']
  choose hZ hE using fun j => hSec l Y (T j) U hU
  choose e he using fun j => hE j W
  have hbij' : ∀ j, Function.Bijective (fun i => e j (zz j i)) :=
    fun j => (e j).bijective.comp (hbij j)
  have alt := hPt W hlW (ptOf hU W (algebraMap Γ(Y, U) W)) hgen φ hφ J (fun j i => e j (zz j i)) hbij'
  unfold AltId at alt
  have hterm : ∀ (j : Fin (n + 1)) (i : J j),
      (twist φ Y)^[n - (j : ℕ)] (resPt W ≫ (e j (zz j i)).1 ≫ (T j).r) =
        ptOf hV (IsLocalRing.ResidueField W) ((φ ^ (n - (j : ℕ))).comp ((IsLocalRing.residue W).comp
          ((zz j i).toRingHom.comp ((T j).r.appLE V ((T j).p ⁻¹ᵁ U) (h j)).hom))) := by
    intro j i
    rw [he j (zz j i)]
    unfold resPt
    rw [(hPtC Y V hV (IsLocalRing.ResidueField W)).2.2 (T j).Z (T j).r ((T j).p ⁻¹ᵁ U) (hZ j) (h j) W
      (IsLocalRing.residue W) (zz j i).toRingHom]
    rw [(hPtC Y V hV (IsLocalRing.ResidueField W)).2.1]
  simp only [hterm] at alt
  classical
  let G : (Spec (CommRingCat.of (IsLocalRing.ResidueField W)) ⟶ Y) → ι → IsLocalRing.ResidueField W :=
    fun P k => if hP : ∃ F, ptOf hV (IsLocalRing.ResidueField W) F = P then (Classical.choose hP) (x k) else 0
  have hG : ∀ F, G (ptOf hV (IsLocalRing.ResidueField W) F) = fun k => F (x k) := by
    intro F
    funext k
    have hP : ∃ F', ptOf hV (IsLocalRing.ResidueField W) F' = ptOf hV (IsLocalRing.ResidueField W) F := ⟨F, rfl⟩
    simp only [G, dif_pos hP]
    rw [(hPtC Y V hV (IsLocalRing.ResidueField W)).1 (Classical.choose_spec hP)]
  have alt2 := congrArg (Multiset.map G) alt
  rw [pts_map, pts_map] at alt2
  simp only [hG, RingHom.comp_apply, hφm, AlgHom.coe_toRingHom] at alt2
  simp only [s, map_pow]
  exact alt2
