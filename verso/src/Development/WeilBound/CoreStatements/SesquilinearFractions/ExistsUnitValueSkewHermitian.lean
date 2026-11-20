import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PointShiftStOfPlaceShiftSt

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf.Aniso

variable {R : Type} [CommRing R] [StarRing R] {I : Type} [Fintype I] [DecidableEq I]

def hf (G : Matrix I I R) (x y : I → R) : R := x ⬝ᵥ G *ᵥ star y

/- English proof (translation)
Simplify using `only [hf, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]`.
-/
theorem hf_expand (G : Matrix I I R) (x y : I → R) : hf G x y = ∑ i, ∑ j, x i * G i j * star (y j) := by
  simp only [hf, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Establish `h : ∀ i j, star (G i j) = -G j i`. Introduce `i j`. Use `congrFun (congrFun hG j) i` as an intermediate fact. Simplify `this` using `[conjTranspose_apply]`. Simplify using `only [hf_expand, star_sum, star_mul', star_star, h]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_skew (G : Matrix I I R) (hG : Gᴴ = -G) (x y : I → R) : hf G y x = -star (hf G x y) := by
  have h : ∀ i j, star (G i j) = -G j i := by
    intro i j
    have := congrFun (congrFun hG j) i
    simpa [conjTranspose_apply] using this
  simp only [hf_expand, star_sum, star_mul', star_star, h]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hf, add_dotProduct]`.
-/
theorem hf_add_left (G : Matrix I I R) (x x' y : I → R) : hf G (x + x') y = hf G x y + hf G x' y := by
  simp only [hf, add_dotProduct]

/- English proof (translation)
Simplify using `only [hf, smul_dotProduct, smul_eq_mul]`.
-/
theorem hf_smul_left (G : Matrix I I R) (a : R) (x y : I → R) : hf G (a • x) y = a * hf G x y := by
  simp only [hf, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', mul_comm]`.
-/
theorem star_smul_vec (a : R) (y : I → R) : star (a • y) = star a • star y := by
  funext i
  simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', mul_comm]

/- English proof (translation)
Simplify using `only [hf, star_add, mulVec_add, dotProduct_add]`.
-/
theorem hf_add_right (G : Matrix I I R) (x y y' : I → R) : hf G x (y + y') = hf G x y + hf G x y' := by
  simp only [hf, star_add, mulVec_add, dotProduct_add]

/- English proof (translation)
Rewrite using `[hf, hf, star_smul_vec, mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem hf_smul_right (G : Matrix I I R) (a : R) (x y : I → R) : hf G x (a • y) = star a * hf G x y := by
  rw [hf, hf, star_smul_vec, mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Take `⟨a, ha⟩` from `hm`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨k⟩` from `‹Nonempty I›`. Use `set e : I → R := Pi.single k 1 with he`.

Use `set v : I → R := e ᵥ* G⁻¹ with hv`. Establish `hse : star e = e`. Use extensionality with `i`. Simplify using `only [he, Pi.star_apply]`. Distinguish the cases in `h : i = k`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`. Establish `hvG : v ᵥ* G = e`. Rewrite using `[hv, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]`.

Establish `hve : hf G v e = 1`. Rewrite using `[hf, hse, Matrix.dotProduct_mulVec, hvG, he]`. Simplify using the standard rewrite rules. Establish `hxy : hf G (a • v) e = a` using `by rw [hf_smul_left, hve, mul_one]`. Establish `hyx : hf G e (a • v) = -star a` using `by rw [hf_skew G hG, hxy]`.

Establish `key : hf G (a • v + e) (a • v + e) = hf G (a • v) (a • v) + a + -star a + hf G e e`. Rewrite using `[hf_add_left, hf_add_right, hf_add_right, hxy, hyx]`. Expand and normalize the polynomial expressions, which then agree. Apply `ha` to reduce the goal to its premises. Establish `h1` using `hcon (a • v + e)`.

Establish `h2` using `hcon (a • v)`. Establish `h3` using `hcon e`. Establish `: a - star a = hf G (a • v + e) (a • v + e) - hf G (a • v) (a • v) - hf G e e`. Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `m.sub_mem (m.sub_mem h1 h2) h3`.
-/
theorem local_exists [Nonempty I] (G : Matrix I I R) (hG : Gᴴ = -G) (hdet : IsUnit G.det) (m : Ideal R)
    (hm : ∃ a : R, a - star a ∉ m) : ∃ x : I → R, hf G x x ∉ m := by
  obtain ⟨a, ha⟩ := hm
  by_contra hcon
  push_neg at hcon
  obtain ⟨k⟩ := ‹Nonempty I›
  set e : I → R := Pi.single k 1 with he
  set v : I → R := e ᵥ* G⁻¹ with hv
  have hse : star e = e := by
    ext i
    simp only [he, Pi.star_apply]
    by_cases h : i = k
    · subst h
      simp
    · simp [Pi.single_apply, h]
  have hvG : v ᵥ* G = e := by
    rw [hv, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  have hve : hf G v e = 1 := by
    rw [hf, hse, Matrix.dotProduct_mulVec, hvG, he]
    simp
  have hxy : hf G (a • v) e = a := by rw [hf_smul_left, hve, mul_one]
  have hyx : hf G e (a • v) = -star a := by rw [hf_skew G hG, hxy]
  have key : hf G (a • v + e) (a • v + e) = hf G (a • v) (a • v) + a + -star a + hf G e e := by
    rw [hf_add_left, hf_add_right, hf_add_right, hxy, hyx]
    ring
  apply ha
  have h1 := hcon (a • v + e)
  have h2 := hcon (a • v)
  have h3 := hcon e
  have : a - star a = hf G (a • v + e) (a • v + e) - hf G (a • v) (a • v) - hf G e e := by
    rw [key]
    ring
  rw [this]
  exact m.sub_mem (m.sub_mem h1 h2) h3

def starI (m : Ideal R) : Ideal R := m.comap (starRingEnd R)

/- English proof (translation)
Use extensionality with `x`. Simplify using `[starI]`.
-/
theorem starI_starI (m : Ideal R) : starI (starI m) = m := by
  ext x
  simp [starI]

/- English proof (translation)
The claim follows from `Ideal.comap_isMaximal_of_surjective _ fun y => ⟨star y, by rw [starRingEnd_apply, star_star]⟩`.
-/
theorem starI_max (m : Ideal R) [m.IsMaximal] : (starI m).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ fun y => ⟨star y, by rw [starRingEnd_apply, star_star]⟩

/- English proof (translation)
Establish `h` using `hf_skew G hG x x`. Establish `h2 : star (hf G x x) = -hf G x x` using `by linear_combination h`. Simplify using `only [starI, Ideal.mem_comap, starRingEnd_apply, h2, neg_mem_iff]`.
-/
theorem mem_starI_iff_of_skew (G : Matrix I I R) (hG : Gᴴ = -G) (m : Ideal R) (x : I → R) :
    hf G x x ∈ starI m ↔ hf G x x ∈ m := by
  have h := hf_skew G hG x x
  have h2 : star (hf G x x) = -hf G x x := by linear_combination h
  simp only [starI, Ideal.mem_comap, starRingEnd_apply, h2, neg_mem_iff]

def orb (m : Ideal R) : Set (Ideal R) := {m, starI m}

/- English proof (translation)
Rewrite using `[orb, orb, starI_starI, Set.pair_comm]`.
-/
theorem orb_starI (m : Ideal R) : orb (starI m) = orb m := by
  rw [orb, orb, starI_starI, Set.pair_comm]

open Classical in

noncomputable def wit (G : Matrix I I R) (S : Set (Ideal R)) : I → R := Classical.epsilon fun x => ∀ n ∈ S, hf G x x ∉ n

/- English proof (translation)
Take `⟨x, hx⟩` from `local_exists G hG hdet m hm`. Establish `hex : ∃ x : I → R, ∀ n ∈ orb m, hf G x x ∉ n`. Use `⟨x, fun n hn => ?_⟩` and prove the remaining obligations. Break down `hn with rfl | rfl` into its components or cases. Conclude with `hx`.

Rewrite using `[mem_starI_iff_of_skew G hG]` and apply the resulting hypothesis. Conclude with `Classical.epsilon_spec hex m (Set.mem_insert _ _)`.
-/
theorem wit_spec [Nonempty I] (G : Matrix I I R) (hG : Gᴴ = -G) (hdet : IsUnit G.det) (m : Ideal R)
    (hm : ∃ a : R, a - star a ∉ m) : hf G (wit G (orb m)) (wit G (orb m)) ∉ m := by
  obtain ⟨x, hx⟩ := local_exists G hG hdet m hm
  have hex : ∃ x : I → R, ∀ n ∈ orb m, hf G x x ∉ n := by
    refine ⟨x, fun n hn => ?_⟩
    rcases hn with rfl | rfl
    · exact hx
    · rwa [mem_starI_iff_of_skew G hG]
  exact Classical.epsilon_spec hex m (Set.mem_insert _ _)

end PositivityTheory.Xgf.Aniso

open PositivityTheory.Xgf.Aniso in
/- English proof (translation)
Introduce `R _ _ _ I _ _ _ G hG hdet hm`. Use `haveI := Fintype.ofFinite (MaximalSpectrum R)`. Establish `crt : ∀ t : MaximalSpectrum R → R, ∃ r : R, ∀ P : MaximalSpectrum R, r - t P ∈ P.asIdeal`. Introduce `t`. Establish `hcop : Pairwise (Function.onFun IsCoprime fun P : MaximalSpectrum R => P.asIdeal)`.

Introduce `P Q hPQ`. Use `haveI := P.isMaximal`. Use `haveI := Q.isMaximal`. Conclude with `Ideal.isCoprime_of_isMaximal (fun h => hPQ (MaximalSpectrum.ext h))`. Take `⟨r, hr⟩` from `Ideal.quotientInfToPiQuotient_surj hcop (fun P => Ideal.Quotient.mk P.asIdeal (t P))`.

Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Use `⟨r, fun P => ?_⟩` and prove the remaining obligations. Establish `h` using `congrFun hr P`. Rewrite `h` using `[Ideal.quotientInfToPiQuotient_mk']`. Conclude with `Ideal.Quotient.eq.mp h`.

Establish `crtO : ∀ O : Set (Ideal R), ∃ c : R, ∀ P : MaximalSpectrum R, (P.asIdeal ∈ O → c - 1 ∈ P.asIdeal) ∧ (P.asIdeal ∉ O → c ∈ P.asIdeal)`. Introduce `O`. Take `⟨r, hr⟩` from `crt (fun P => if P.asIdeal ∈ O then 1 else 0)`. Use `⟨r, fun P => ⟨fun h => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Simplify `hr P` using `[h]`.

Simplify `hr P` using `[h]`. Use `choose c hc using crtO`. Set `S : Finset (Set (Ideal R))` to `Finset.univ.image (fun P : MaximalSpectrum R => orb P.asIdeal)`. Use `⟨∑ O ∈ S, c O • wit G O, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnu`.

Take `⟨M, hM, hxM⟩` from `exists_max_ideal_of_mem_nonunits hnu`. Establish `hM' : (starI M).IsMaximal` using `starI_max M`. Set `P : MaximalSpectrum R` to `⟨M, hM⟩`. Set `P' : MaximalSpectrum R` to `⟨starI M, hM'⟩`. Establish `hO0 : orb M ∈ S` using `Finset.mem_image.mpr ⟨P, Finset.mem_univ _, rfl⟩`.

Establish `hw : hf G (wit G (orb M)) (wit G (orb M)) ∉ M` using `wit_spec G hG hdet M (hm M hM)`. Establish `hoff : ∀ O ∈ S, O ≠ orb M → M ∉ O ∧ starI M ∉ O`. Introduce `O hO hne`. Take `⟨Q, _, rfl⟩` from `Finset.mem_image.mp hO`. Prove the components needed by the constructor for the conclusion.

Introduce `hMQ`. Apply `hne` to reduce the goal to its premises. Simplify using `only [orb, Set.mem_insert_iff, Set.mem_singleton_iff] at hMQ`. Break down `hMQ with h | h` into its components or cases. Rewrite using `[h]`.

Rewrite using `[h, orb_starI]`. Introduce `hMQ`. Apply `hne` to reduce the goal to its premises. Simplify using `only [orb, Set.mem_insert_iff, Set.mem_singleton_iff] at hMQ`. Break down `hMQ with h | h` into its components or cases.

Rewrite using `[← h, orb_starI]`. Establish `h' : M = Q.asIdeal` using `by rw [← starI_starI M, h, starI_starI]`. Rewrite using `[h']`. Establish `hz1 : ∀ y, hf G (∑ O ∈ S.erase (orb M), c O • wit G O) y ∈ M`. Introduce `y`.

Use `Finset.sum_induction _ (fun v => hf G v y ∈ M) (fun a b ha hb => by rw [hf_add_left]; exact M.add_mem ha hb) (by simp [hf]) (fun O hO => ?_)` and prove the remaining obligations. Establish `hne` using `Finset.ne_of_mem_erase hO`. Establish `hOS` using `Finset.mem_of_mem_erase hO`. Rewrite using `[hf_smul_left]`. Conclude with `M.mul_mem_right _ ((hc O P).2 (hoff O hOS hne).1)`.

Establish `hz2 : ∀ y, hf G y (∑ O ∈ S.erase (orb M), c O • wit G O) ∈ M`. Introduce `y`. Use `Finset.sum_induction _ (fun v => hf G y v ∈ M) (fun a b ha hb => by rw [hf_add_right]; exact M.add_mem ha hb) (by simp [hf]) (fun O hO => ?_)` and prove the remaining obligations. Establish `hne` using `Finset.ne_of_mem_erase hO`. Establish `hOS` using `Finset.mem_of_mem_erase hO`.

Rewrite using `[hf_smul_right]`. Conclude with `M.mul_mem_right _ (Ideal.mem_comap.mp ((hc O P').2 (hoff O hOS hne).2))`. Establish `hc1 : c (orb M) - 1 ∈ M` using `(hc (orb M) P).1 (Set.mem_insert _ _)`. Establish `hc2 : star (c (orb M)) - 1 ∈ M`. Establish `h` using `Ideal.mem_comap.mp ((hc (orb M) P').1 (Set.mem_insert_of_mem _ rfl))`.

Simplify `h` using `[starRingEnd_apply, star_sub, star_one]`. Establish `hsplit : ∑ O ∈ S, c O • wit G O = c (orb M) • wit G (orb M) + ∑ O ∈ S.erase (orb M), c O • wit G O` using `(Finset.add_sum_erase S _ hO0).symm`. Establish `hxM' : hf G (∑ O ∈ S, c O • wit G O) (∑ O ∈ S, c O • wit G O) ∈ M` using `hxM`. Rewrite `hxM'` using `[hsplit]`. Use `set w := wit G (orb M)`.

Use `set z := ∑ O ∈ S.erase (orb M), c O • wit G O`. Use `set a := c (orb M)`. Establish `expand : hf G (a • w + z) (a • w + z) = a * (star a * hf G w w) + hf G (a • w) z + (hf G z (a • w) + hf G z z)`. Rewrite using `[hf_add_left, hf_add_right, hf_add_right, hf_smul_left G a w (a • w), hf_smul_right]`. Apply `hw` to reduce the goal to its premises.

Establish `e2 : hf G w w = hf G (a • w + z) (a • w + z) - (a * (star a - 1) + (a - 1)) * hf G w w - hf G (a • w) z - (hf G z (a • w) + hf G z z)`. Rewrite using `[expand]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `M.sub_mem (M.sub_mem (M.sub_mem hxM' (M.mul_mem_right _ (M.add_mem (M.mul_mem_left _ hc2) hc1))) (hz2 _)) (M.add_mem (hz1 _) (hz1 _))`.
-/
theorem PositivityTheory.Xgf.exists_unit_value_skew_hermitian : ∀ (R : Type) [CommRing R] [StarRing R] [Finite (MaximalSpectrum R)] (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] (G : Matrix I I R), Gᴴ = -G → IsUnit G.det → (∀ m : Ideal R, m.IsMaximal → ∃ a : R, a - star a ∉ m) → ∃ x : I → R, IsUnit (x ⬝ᵥ G.mulVec (star x)) := by
  intro R _ _ _ I _ _ _ G hG hdet hm
  classical
  haveI := Fintype.ofFinite (MaximalSpectrum R)
  have crt : ∀ t : MaximalSpectrum R → R, ∃ r : R, ∀ P : MaximalSpectrum R, r - t P ∈ P.asIdeal := by
    intro t
    have hcop : Pairwise (Function.onFun IsCoprime fun P : MaximalSpectrum R => P.asIdeal) := by
      intro P Q hPQ
      haveI := P.isMaximal
      haveI := Q.isMaximal
      exact Ideal.isCoprime_of_isMaximal (fun h => hPQ (MaximalSpectrum.ext h))
    obtain ⟨r, hr⟩ := Ideal.quotientInfToPiQuotient_surj hcop (fun P => Ideal.Quotient.mk P.asIdeal (t P))
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine ⟨r, fun P => ?_⟩
    have h := congrFun hr P
    rw [Ideal.quotientInfToPiQuotient_mk'] at h
    exact Ideal.Quotient.eq.mp h
  have crtO : ∀ O : Set (Ideal R), ∃ c : R, ∀ P : MaximalSpectrum R,
      (P.asIdeal ∈ O → c - 1 ∈ P.asIdeal) ∧ (P.asIdeal ∉ O → c ∈ P.asIdeal) := by
    intro O
    obtain ⟨r, hr⟩ := crt (fun P => if P.asIdeal ∈ O then 1 else 0)
    refine ⟨r, fun P => ⟨fun h => ?_, fun h => ?_⟩⟩
    · simpa [h] using hr P
    · simpa [h] using hr P
  choose c hc using crtO
  let S : Finset (Set (Ideal R)) := Finset.univ.image (fun P : MaximalSpectrum R => orb P.asIdeal)
  refine ⟨∑ O ∈ S, c O • wit G O, ?_⟩
  by_contra hnu
  obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits hnu
  have hM' : (starI M).IsMaximal := starI_max M
  let P : MaximalSpectrum R := ⟨M, hM⟩
  let P' : MaximalSpectrum R := ⟨starI M, hM'⟩
  have hO0 : orb M ∈ S := Finset.mem_image.mpr ⟨P, Finset.mem_univ _, rfl⟩
  have hw : hf G (wit G (orb M)) (wit G (orb M)) ∉ M := wit_spec G hG hdet M (hm M hM)
  have hoff : ∀ O ∈ S, O ≠ orb M → M ∉ O ∧ starI M ∉ O := by
    intro O hO hne
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hO
    constructor
    · intro hMQ
      apply hne
      simp only [orb, Set.mem_insert_iff, Set.mem_singleton_iff] at hMQ
      rcases hMQ with h | h
      · rw [h]
      · rw [h, orb_starI]
    · intro hMQ
      apply hne
      simp only [orb, Set.mem_insert_iff, Set.mem_singleton_iff] at hMQ
      rcases hMQ with h | h
      · rw [← h, orb_starI]
      · have h' : M = Q.asIdeal := by rw [← starI_starI M, h, starI_starI]
        rw [h']
  have hz1 : ∀ y, hf G (∑ O ∈ S.erase (orb M), c O • wit G O) y ∈ M := by
    intro y
    refine Finset.sum_induction _ (fun v => hf G v y ∈ M)
      (fun a b ha hb => by rw [hf_add_left]; exact M.add_mem ha hb) (by simp [hf]) (fun O hO => ?_)
    have hne := Finset.ne_of_mem_erase hO
    have hOS := Finset.mem_of_mem_erase hO
    rw [hf_smul_left]
    exact M.mul_mem_right _ ((hc O P).2 (hoff O hOS hne).1)
  have hz2 : ∀ y, hf G y (∑ O ∈ S.erase (orb M), c O • wit G O) ∈ M := by
    intro y
    refine Finset.sum_induction _ (fun v => hf G y v ∈ M)
      (fun a b ha hb => by rw [hf_add_right]; exact M.add_mem ha hb) (by simp [hf]) (fun O hO => ?_)
    have hne := Finset.ne_of_mem_erase hO
    have hOS := Finset.mem_of_mem_erase hO
    rw [hf_smul_right]
    exact M.mul_mem_right _ (Ideal.mem_comap.mp ((hc O P').2 (hoff O hOS hne).2))
  have hc1 : c (orb M) - 1 ∈ M := (hc (orb M) P).1 (Set.mem_insert _ _)
  have hc2 : star (c (orb M)) - 1 ∈ M := by
    have h := Ideal.mem_comap.mp ((hc (orb M) P').1 (Set.mem_insert_of_mem _ rfl))
    simpa [starRingEnd_apply, star_sub, star_one] using h
  have hsplit : ∑ O ∈ S, c O • wit G O = c (orb M) • wit G (orb M) + ∑ O ∈ S.erase (orb M), c O • wit G O :=
    (Finset.add_sum_erase S _ hO0).symm
  have hxM' : hf G (∑ O ∈ S, c O • wit G O) (∑ O ∈ S, c O • wit G O) ∈ M := hxM
  rw [hsplit] at hxM'
  set w := wit G (orb M)
  set z := ∑ O ∈ S.erase (orb M), c O • wit G O
  set a := c (orb M)
  have expand : hf G (a • w + z) (a • w + z) =
      a * (star a * hf G w w) + hf G (a • w) z + (hf G z (a • w) + hf G z z) := by
    rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left G a w (a • w), hf_smul_right]
  apply hw
  have e2 : hf G w w = hf G (a • w + z) (a • w + z) - (a * (star a - 1) + (a - 1)) * hf G w w
      - hf G (a • w) z - (hf G z (a • w) + hf G z z) := by
    rw [expand]
    ring
  rw [e2]
  exact M.sub_mem (M.sub_mem (M.sub_mem hxM' (M.mul_mem_right _ (M.add_mem (M.mul_mem_left _ hc2) hc1))) (hz2 _))
    (M.add_mem (hz1 _) (hz1 _))

namespace PositivityTheory.Xgf.Diag

open PositivityTheory.Xgf.Aniso

variable {R : Type} [CommRing R] [StarRing R]

/- English proof (translation)
Assume the negation of the conclusion as `h'`. Take `⟨M, hM, hrM⟩` from `exists_max_ideal_of_mem_nonunits h'`. Conclude with `h M hM hrM`.
-/
theorem isUnit_of_forall_notMem (r : R) (h : ∀ M : Ideal R, M.IsMaximal → r ∉ M) : IsUnit r := by
  by_contra h'
  obtain ⟨M, hM, hrM⟩ := exists_max_ideal_of_mem_nonunits h'
  exact h M hM hrM

/- English proof (translation)
Establish `hI : Pairwise (Function.onFun IsCoprime fun P : MaximalSpectrum R => P.asIdeal)`. Introduce `P Q hPQ`. Use `haveI := P.isMaximal`. Use `haveI := Q.isMaximal`. Conclude with `Ideal.isCoprime_of_isMaximal (fun h => hPQ (MaximalSpectrum.ext h))`.

Conclude with `Ideal.exists_forall_sub_mem_ideal hI t`.
-/
theorem crt_entry [Finite (MaximalSpectrum R)] (t : MaximalSpectrum R → R) :
    ∃ r : R, ∀ P : MaximalSpectrum R, r - t P ∈ P.asIdeal := by
  have hI : Pairwise (Function.onFun IsCoprime fun P : MaximalSpectrum R => P.asIdeal) := by
    intro P Q hPQ
    haveI := P.isMaximal
    haveI := Q.isMaximal
    exact Ideal.isCoprime_of_isMaximal (fun h => hPQ (MaximalSpectrum.ext h))
  exact Ideal.exists_forall_sub_mem_ideal hI t

/- English proof (translation)
Introduce `M hM`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hmem : hf G x x ∈ M`. Rewrite using `[hf_expand]`.

Conclude with `Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => M.mul_mem_right _ (M.mul_mem_right _ (h i))`. Conclude with `hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)`.
-/
theorem unimod {I : Type} [Fintype I] [DecidableEq I] (G : Matrix I I R) (x : I → R) (hu : IsUnit (hf G x x)) :
    ∀ M : Ideal R, M.IsMaximal → ∃ i, x i ∉ M := by
  intro M hM
  by_contra h
  push_neg at h
  have hmem : hf G x x ∈ M := by
    rw [hf_expand]
    exact Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => M.mul_mem_right _ (M.mul_mem_right _ (h i))
  exact hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)

/- English proof (translation)
Establish `hk : ∀ P : MaximalSpectrum R, ∃ k : Fin (n + 1), x k ∉ P.asIdeal ∧ (k ≠ 0 → x 0 ∈ P.asIdeal)`. Introduce `P`. Distinguish the cases in `h0 : x 0 ∈ P.asIdeal`. Take `⟨i, hi⟩` from `hx P.asIdeal P.isMaximal`. Conclude with `⟨i, hi, fun _ => h0⟩`.

Conclude with `⟨0, h0, fun h => absurd rfl h⟩`. Use `choose k hkx hk0 using hk`. Apply the tactic sequence `have hc : ∀ i : Fin (n + 1), ∃ r : R, ∀ P : MaximalSpectrum R, r - (if i = k P then 1 else 0) ∈ P.asIdeal := fun i => crt_entry (fun P => if i = k P then 1 else 0)`. Use `choose c hc using hc`. Set `c' : Fin (n + 1) → R` to `fun i => if i = 0 then 1 else c i`.

Set `B : Matrix (Fin (n + 1)) (Fin (n + 1)) R` to `fun i j => if j = 0 then c' i else (1 : Matrix _ _ R) i j`. Use `⟨B, ?_, ?_⟩` and prove the remaining obligations. Establish `hB : B.BlockTriangular OrderDual.toDual`. Introduce `i j hij`. Establish `hij' : i < j` using `OrderDual.toDual_lt_toDual.mp hij`.

Establish `hj : j ≠ 0`. Introduce and unpack `rfl`. Conclude with `Fin.not_lt_zero _ hij'`. Simplify using `[B, hj, Matrix.one_apply, ne_of_lt hij']`. Establish `hd : ∀ i, B i i = 1`.

Introduce `i`. Apply the tactic sequence `by_cases h : i = 0 <;> simp [B, c', h]`. Rewrite using `[Matrix.det_of_lowerTriangular B hB]`. Simplify using `[hd]`. Establish `hy : (x ᵥ* B) 0 = ∑ i, x i * c' i`.

Simplify using `[Matrix.vecMul, dotProduct, B]`. Rewrite using `[hy]`. Apply `isUnit_of_forall_notMem` to reduce the goal to its premises. Introduce `M hM`. Set `P : MaximalSpectrum R` to `⟨M, hM⟩`.

Establish `hterm : ∀ i, x i * c' i - (if i = k P then x i else 0) ∈ M`. Introduce `i`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Distinguish the cases in `h0 : (0 : Fin (n + 1)) = k P`.

Rewrite using `[if_pos h0]`. Simplify using `[c']`. Rewrite using `[if_neg h0]`. Simplify `hk0 P (Ne.symm h0)` using `[c']`. Establish `h : x i * (c i - if i = k P then 1 else 0) ∈ M` using `Ideal.mul_mem_left _ (x i) (hc i P)`.

Establish `he : x i * c' i - (if i = k P then x i else 0) = x i * (c i - if i = k P then 1 else 0)`. Simplify using `only [c', if_neg hi]`. Apply the tactic sequence `split_ifs <;> ring`. Rewrite using `[he]`. Conclude with `h`.

Establish `hsum : (∑ i, x i * c' i) - x (k P) ∈ M`. Use `Ideal.sum_mem M (t := Finset.univ) (fun i _ => hterm i)` as an intermediate fact. Simplify `this` using `[Finset.sum_sub_distrib]`. Introduce `hmem`. Apply `hkx P` to reduce the goal to its premises.

Use `M.sub_mem hmem hsum` as an intermediate fact. Simplify using `using this`.
-/
theorem unitCoord [Finite (MaximalSpectrum R)] {n : ℕ} (x : Fin (n + 1) → R)
    (hx : ∀ M : Ideal R, M.IsMaximal → ∃ i, x i ∉ M) :
    ∃ B : Matrix (Fin (n + 1)) (Fin (n + 1)) R, IsUnit B.det ∧ IsUnit ((x ᵥ* B) 0) := by
  classical
  have hk : ∀ P : MaximalSpectrum R, ∃ k : Fin (n + 1), x k ∉ P.asIdeal ∧ (k ≠ 0 → x 0 ∈ P.asIdeal) := by
    intro P
    by_cases h0 : x 0 ∈ P.asIdeal
    · obtain ⟨i, hi⟩ := hx P.asIdeal P.isMaximal
      exact ⟨i, hi, fun _ => h0⟩
    · exact ⟨0, h0, fun h => absurd rfl h⟩
  choose k hkx hk0 using hk
  have hc : ∀ i : Fin (n + 1), ∃ r : R, ∀ P : MaximalSpectrum R,
      r - (if i = k P then 1 else 0) ∈ P.asIdeal :=
    fun i => crt_entry (fun P => if i = k P then 1 else 0)
  choose c hc using hc
  let c' : Fin (n + 1) → R := fun i => if i = 0 then 1 else c i
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j => if j = 0 then c' i else (1 : Matrix _ _ R) i j
  refine ⟨B, ?_, ?_⟩
  · have hB : B.BlockTriangular OrderDual.toDual := by
      intro i j hij
      have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
      have hj : j ≠ 0 := by
        rintro rfl
        exact Fin.not_lt_zero _ hij'
      simp [B, hj, Matrix.one_apply, ne_of_lt hij']
    have hd : ∀ i, B i i = 1 := by
      intro i
      by_cases h : i = 0 <;> simp [B, c', h]
    rw [Matrix.det_of_lowerTriangular B hB]
    simp [hd]
  · have hy : (x ᵥ* B) 0 = ∑ i, x i * c' i := by
      simp [Matrix.vecMul, dotProduct, B]
    rw [hy]
    apply isUnit_of_forall_notMem
    intro M hM
    let P : MaximalSpectrum R := ⟨M, hM⟩
    have hterm : ∀ i, x i * c' i - (if i = k P then x i else 0) ∈ M := by
      intro i
      by_cases hi : i = 0
      · subst hi
        by_cases h0 : (0 : Fin (n + 1)) = k P
        · rw [if_pos h0]
          simp [c']
        · rw [if_neg h0]
          simpa [c'] using hk0 P (Ne.symm h0)
      · have h : x i * (c i - if i = k P then 1 else 0) ∈ M := Ideal.mul_mem_left _ (x i) (hc i P)
        have he : x i * c' i - (if i = k P then x i else 0) = x i * (c i - if i = k P then 1 else 0) := by
          simp only [c', if_neg hi]
          split_ifs <;> ring
        rw [he]
        exact h
    have hsum : (∑ i, x i * c' i) - x (k P) ∈ M := by
      have := Ideal.sum_mem M (t := Finset.univ) (fun i _ => hterm i)
      simpa [Finset.sum_sub_distrib] using this
    intro hmem
    apply hkx P
    have := M.sub_mem hmem hsum
    simpa using this

/- English proof (translation)
Rewrite using `[hf_expand]`. Simplify using `only [mul_apply, conjTranspose_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem mul_conj_apply {I : Type} [Fintype I] [DecidableEq I] (T G : Matrix I I R) (i j : I) :
    (T * G * Tᴴ) i j = hf G (T i) (T j) := by
  rw [hf_expand]
  simp only [mul_apply, conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Use `set a := hf G x x with ha`. Use `set ainv : R := ↑hu.unit⁻¹ with hainv`. Establish `haa : a * ainv = 1` using `hu.mul_val_inv`. Set `L : Matrix (Fin (n + 1)) (Fin (n + 1)) R` to `fun i k => if i = k then 1 else if k = 0 then -(hf G (Pi.single i 1) x * ainv) else 0`. Set `P : Matrix (Fin (n + 1)) (Fin (n + 1)) R` to `fun i => if i = 0 then x else Pi.single i 1`.

Establish `hL : L.det = 1`. Rewrite using `[Matrix.det_of_lowerTriangular L]`. Conclude with `Finset.prod_eq_one fun i _ => by simp [L]`. Introduce `i k hik`. Establish `hik' : i < k` using `OrderDual.toDual_lt_toDual.mp hik`.

Establish `hne : i ≠ k` using `ne_of_lt hik'`. Establish `hk : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `absurd hik' (Fin.not_lt_zero _)`. Simplify using `[L, hne, hk]`.

Establish `hP : P.det = x 0`. Rewrite using `[Matrix.det_of_upperTriangular]`. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `[P, Fin.succ_ne_zero]`. Introduce `i k hki`.

Establish `hi : i ≠ 0`. Introduce and unpack `rfl`. Conclude with `absurd hki (Fin.not_lt_zero _)`. Establish `hne : k ≠ i` using `ne_of_lt hki`. Simplify using `[P, hi, Pi.single_apply, hne]`.

Establish `hr0 : (L * P) 0 = x`. Use extensionality with `k`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_succ]`. Simplify using `[L, P, Fin.succ_ne_zero]`. Conclude with `Finset.sum_eq_zero fun m _ => by simp [(Fin.succ_ne_zero m).symm]`.

Establish `hrs : ∀ j : Fin n, (L * P) j.succ = Pi.single j.succ 1 - (hf G (Pi.single j.succ 1) x * ainv) • x`. Introduce `j`. Use extensionality with `k`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_succ]`. Simplify using `[L, P, Fin.succ_ne_zero]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨L * P, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, hL, hP, one_mul]`. Conclude with `hx0`. Introduce `j`.

Rewrite using `[mul_conj_apply, hr0, hrs, sub_eq_add_neg, ← neg_smul, hf_add_left, hf_smul_left]`. Take the linear combination `(-(hf G (Pi.single j.succ 1) x)) * haa`. Introduce `j`. Rewrite using `[mul_conj_apply, hr0, hrs, sub_eq_add_neg, ← neg_smul, hf_add_right, hf_smul_right]`. Establish `h1 : hf G x (Pi.single j.succ 1) = -star (hf G (Pi.single j.succ 1) x)` using `hf_skew G hG (Pi.single j.succ 1) x`.

Establish `h2 : a = -star a` using `hf_skew G hG x x`. Establish `h3 : star a * star ainv = 1` using `by rw [← star_mul', haa, star_one]`. Rewrite using `[h1, star_neg, star_mul']`. Take the linear combination `(-(star (hf G (Pi.single j.succ 1) x) * star ainv)) * h2 + star (hf G (Pi.single j.succ 1) x) * h3`.
-/
theorem step {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hG : Gᴴ = -G) (x : Fin (n + 1) → R)
    (hx0 : IsUnit (x 0)) (hu : IsUnit (hf G x x)) :
    ∃ T : Matrix (Fin (n + 1)) (Fin (n + 1)) R, IsUnit T.det ∧ (∀ j : Fin n, (T * G * Tᴴ) j.succ 0 = 0) ∧
      ∀ j : Fin n, (T * G * Tᴴ) 0 j.succ = 0 := by
  set a := hf G x x with ha
  set ainv : R := ↑hu.unit⁻¹ with hainv
  have haa : a * ainv = 1 := hu.mul_val_inv
  let L : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i k =>
    if i = k then 1 else if k = 0 then -(hf G (Pi.single i 1) x * ainv) else 0
  let P : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i => if i = 0 then x else Pi.single i 1
  have hL : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L]
    · exact Finset.prod_eq_one fun i _ => by simp [L]
    · intro i k hik
      have hik' : i < k := OrderDual.toDual_lt_toDual.mp hik
      have hne : i ≠ k := ne_of_lt hik'
      have hk : k ≠ 0 := by
        rintro rfl
        exact absurd hik' (Fin.not_lt_zero _)
      simp [L, hne, hk]
  have hP : P.det = x 0 := by
    rw [Matrix.det_of_upperTriangular]
    · rw [Fin.prod_univ_succ]
      simp [P, Fin.succ_ne_zero]
    · intro i k hki
      have hi : i ≠ 0 := by
        rintro rfl
        exact absurd hki (Fin.not_lt_zero _)
      have hne : k ≠ i := ne_of_lt hki
      simp [P, hi, Pi.single_apply, hne]
  have hr0 : (L * P) 0 = x := by
    ext k
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [L, P, Fin.succ_ne_zero]
    exact Finset.sum_eq_zero fun m _ => by simp [(Fin.succ_ne_zero m).symm]
  have hrs : ∀ j : Fin n, (L * P) j.succ =
      Pi.single j.succ 1 - (hf G (Pi.single j.succ 1) x * ainv) • x := by
    intro j
    ext k
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [L, P, Fin.succ_ne_zero]
    ring
  refine ⟨L * P, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, hL, hP, one_mul]
    exact hx0
  · intro j
    rw [mul_conj_apply, hr0, hrs, sub_eq_add_neg, ← neg_smul, hf_add_left, hf_smul_left]
    linear_combination (-(hf G (Pi.single j.succ 1) x)) * haa
  · intro j
    rw [mul_conj_apply, hr0, hrs, sub_eq_add_neg, ← neg_smul, hf_add_right, hf_smul_right]
    have h1 : hf G x (Pi.single j.succ 1) = -star (hf G (Pi.single j.succ 1) x) :=
      hf_skew G hG (Pi.single j.succ 1) x
    have h2 : a = -star a := hf_skew G hG x x
    have h3 : star a * star ainv = 1 := by rw [← star_mul', haa, star_one]
    rw [h1, star_neg, star_mul']
    linear_combination (-(star (hf G (Pi.single j.succ 1) x) * star ainv)) * h2 +
      star (hf G (Pi.single j.succ 1) x) * h3

end PositivityTheory.Xgf.Diag

open PositivityTheory.Xgf.Aniso PositivityTheory.Xgf.Diag in
/- English proof (translation)
Introduce `R _ _ _ n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `G _ _ _`. Use `⟨1, by simp, ?_⟩` and prove the remaining obligations.

Introduce `i`. Conclude with `Fin.elim0 i`. Consider the case `succ n ih`. Introduce `G hG hdet hR`. Establish `hcong : ∀ (S M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (u v : Fin (n + 1) → R), hf (S * M * Sᴴ) u v = hf M (u ᵥ* S) (v ᵥ* S)`.

Introduce `S M u v`. Simplify using `only [hf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_vecMul]`. Establish `hskew : ∀ (S M : Matrix (Fin (n + 1)) (Fin (n + 1)) R), Mᴴ = -M → (S * M * Sᴴ)ᴴ = -(S * M * Sᴴ)`. Introduce `S M hM`. Simplify using `[Matrix.conjTranspose_mul, hM, Matrix.mul_assoc]`.

Establish `hdetc : ∀ (S M : Matrix (Fin (n + 1)) (Fin (n + 1)) R), IsUnit S.det → IsUnit M.det → IsUnit (S * M * Sᴴ).det`. Introduce `S M hS hM`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`. Conclude with `(hS.mul hM).mul (isUnit_star.mpr hS)`. Take `⟨x, hx⟩` from `PositivityTheory.Xgf.exists_unit_value_skew_hermitian R (Fin (n + 1)) G hG hdet hR`.

Establish `hxu : IsUnit (hf G x x)` using `hx`. Take `⟨B, hB, hB0⟩` from `unitCoord x (unimod G x hxu)`. Establish `hBi : IsUnit B⁻¹.det` using `Matrix.isUnit_nonsing_inv_det B hB`. Use `set G1 := B⁻¹ * G * (B⁻¹)ᴴ with hG1`. Establish `hu1 : IsUnit (hf G1 (x ᵥ* B) (x ᵥ* B))`.

Rewrite using `[hG1, hcong, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv B hB, Matrix.vecMul_one]`. Conclude with `hxu`. Take `⟨T1, hT1, hT1a, hT1b⟩` from `step G1 (hskew _ _ hG) (x ᵥ* B) hB0 hu1`. Use `set G2 := T1 * G1 * T1ᴴ with hG2`. Establish `hG2s : G2ᴴ = -G2` using `hskew _ _ (hskew _ _ hG)`.

Establish `hG2d : IsUnit G2.det` using `hdetc _ _ hT1 (hdetc _ _ hBi hdet)`. Use `set G3 := G2.submatrix Fin.succ Fin.succ with hG3`. Establish `hG3s : G3ᴴ = -G3`. Rewrite using `[hG3, Matrix.conjTranspose_submatrix, hG2s]`. Both sides reduce to the same expression.

Establish `hdet23 : G2.det = G2 0 0 * G3.det`. Rewrite using `[Matrix.det_succ_column_zero, Fin.sum_univ_succ]`. Establish `: ∀ i : Fin n, G2 i.succ 0 = 0` using `hT1a`. Simplify using `[this, Fin.succAbove_zero, hG3]`. Establish `hG3d : IsUnit G3.det`.

Rewrite `hG2d` using `[hdet23]`. Conclude with `isUnit_of_mul_isUnit_right hG2d`. Take `⟨T3, hT3, hT3d⟩` from `ih G3 hG3s hG3d hR`. Set `D : Matrix (Fin (n + 1)) (Fin (n + 1)) R` to `fun i => Fin.cons (α := fun _ => Fin (n + 1) → R) (Pi.single 0 1) (fun i' => Fin.cons (α := fun _ => R) 0 (T3 i')) i`. Establish `hD0 : D 0 = Pi.single 0 1` using `by simp [D]`.

Establish `hDs : ∀ i' : Fin n, D i'.succ = Fin.cons 0 (T3 i')` using `by intro i'; simp [D]`. Establish `hDdet : D.det = T3.det`. Rewrite using `[Matrix.det_succ_row_zero, Fin.sum_univ_succ, hD0]`. Establish `: D.submatrix Fin.succ Fin.succ = T3`. Use extensionality with `i j`.

Simplify using `[hDs]`. Simplify using `[Fin.succAbove_zero, this, Fin.succ_ne_zero]`. Establish `hcons : ∀ u v : Fin n → R, hf G2 (Fin.cons 0 u) (Fin.cons 0 v) = hf G3 u v`. Introduce `u v`. Simplify using `only [hf_expand, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero, hG3, Matrix.submatrix_apply]`.

Establish `hleft : ∀ v : Fin n → R, hf G2 (Pi.single 0 1) (Fin.cons 0 v) = 0`. Introduce `v`. Establish `: ∀ j : Fin n, G2 0 j.succ = 0` using `hT1b`. Simplify using `[hf_expand, Fin.sum_univ_succ, Pi.single_apply, Fin.succ_ne_zero, this]`. Establish `hright : ∀ u : Fin n → R, hf G2 (Fin.cons 0 u) (Pi.single 0 1) = 0`.

Introduce `u`. Establish `: ∀ j : Fin n, G2 j.succ 0 = 0` using `hT1a`. Simplify using `[hf_expand, Fin.sum_univ_succ, Pi.single_apply, Fin.succ_ne_zero, this]`. Use `⟨D * (T1 * B⁻¹), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, Matrix.det_mul, hDdet]`.

Conclude with `hT3.mul (hT1.mul hBi)`. Establish `heq : D * (T1 * B⁻¹) * G * (D * (T1 * B⁻¹))ᴴ = D * G2 * Dᴴ`. Simplify using `only [hG2, hG1, Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[heq]`. Introduce `i j hij`.

Rewrite using `[mul_conj_apply]`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => exact absurd rfl hij`.

Consider the case `succ j' => rw [hD0, hDs, hleft]`. Consider the case `succ i'`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => rw [hD0, hDs, hright]`. Consider the case `succ j'`.

Rewrite using `[hDs, hDs, hcons, ← mul_conj_apply]`. Conclude with `hT3d (fun h => hij (by rw [h]))`.
-/
theorem PositivityTheory.Xgf.skew_hermitian_diagonalizable : ∀ (R : Type) [CommRing R] [StarRing R] [Finite (MaximalSpectrum R)] (n : ℕ) (G : Matrix (Fin n) (Fin n) R), Gᴴ = -G → IsUnit G.det → (∀ m : Ideal R, m.IsMaximal → ∃ a : R, a - star a ∉ m) → ∃ T : Matrix (Fin n) (Fin n) R, IsUnit T.det ∧ (T * G * Tᴴ).IsDiag := by
  intro R _ _ _ n
  induction n with
  | zero =>
    intro G _ _ _
    refine ⟨1, by simp, ?_⟩
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    intro G hG hdet hR
    have hcong : ∀ (S M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (u v : Fin (n + 1) → R),
        hf (S * M * Sᴴ) u v = hf M (u ᵥ* S) (v ᵥ* S) := by
      intro S M u v
      simp only [hf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_vecMul]
    have hskew : ∀ (S M : Matrix (Fin (n + 1)) (Fin (n + 1)) R), Mᴴ = -M →
        (S * M * Sᴴ)ᴴ = -(S * M * Sᴴ) := by
      intro S M hM
      simp [Matrix.conjTranspose_mul, hM, Matrix.mul_assoc]
    have hdetc : ∀ (S M : Matrix (Fin (n + 1)) (Fin (n + 1)) R), IsUnit S.det → IsUnit M.det →
        IsUnit (S * M * Sᴴ).det := by
      intro S M hS hM
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
      exact (hS.mul hM).mul (isUnit_star.mpr hS)
    obtain ⟨x, hx⟩ := PositivityTheory.Xgf.exists_unit_value_skew_hermitian R (Fin (n + 1)) G hG hdet hR
    have hxu : IsUnit (hf G x x) := hx
    obtain ⟨B, hB, hB0⟩ := unitCoord x (unimod G x hxu)
    have hBi : IsUnit B⁻¹.det := Matrix.isUnit_nonsing_inv_det B hB
    set G1 := B⁻¹ * G * (B⁻¹)ᴴ with hG1
    have hu1 : IsUnit (hf G1 (x ᵥ* B) (x ᵥ* B)) := by
      rw [hG1, hcong, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv B hB, Matrix.vecMul_one]
      exact hxu
    obtain ⟨T1, hT1, hT1a, hT1b⟩ := step G1 (hskew _ _ hG) (x ᵥ* B) hB0 hu1
    set G2 := T1 * G1 * T1ᴴ with hG2
    have hG2s : G2ᴴ = -G2 := hskew _ _ (hskew _ _ hG)
    have hG2d : IsUnit G2.det := hdetc _ _ hT1 (hdetc _ _ hBi hdet)
    set G3 := G2.submatrix Fin.succ Fin.succ with hG3
    have hG3s : G3ᴴ = -G3 := by
      rw [hG3, Matrix.conjTranspose_submatrix, hG2s]
      rfl
    have hdet23 : G2.det = G2 0 0 * G3.det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      have : ∀ i : Fin n, G2 i.succ 0 = 0 := hT1a
      simp [this, Fin.succAbove_zero, hG3]
    have hG3d : IsUnit G3.det := by
      rw [hdet23] at hG2d
      exact isUnit_of_mul_isUnit_right hG2d
    obtain ⟨T3, hT3, hT3d⟩ := ih G3 hG3s hG3d hR
    let D : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i =>
      Fin.cons (α := fun _ => Fin (n + 1) → R) (Pi.single 0 1)
        (fun i' => Fin.cons (α := fun _ => R) 0 (T3 i')) i
    have hD0 : D 0 = Pi.single 0 1 := by simp [D]
    have hDs : ∀ i' : Fin n, D i'.succ = Fin.cons 0 (T3 i') := by intro i'; simp [D]
    have hDdet : D.det = T3.det := by
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, hD0]
      have : D.submatrix Fin.succ Fin.succ = T3 := by
        ext i j
        simp [hDs]
      simp [Fin.succAbove_zero, this, Fin.succ_ne_zero]
    have hcons : ∀ u v : Fin n → R, hf G2 (Fin.cons 0 u) (Fin.cons 0 v) = hf G3 u v := by
      intro u v
      simp only [hf_expand, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, star_zero, zero_mul,
        mul_zero, Finset.sum_const_zero, zero_add, add_zero, hG3, Matrix.submatrix_apply]
    have hleft : ∀ v : Fin n → R, hf G2 (Pi.single 0 1) (Fin.cons 0 v) = 0 := by
      intro v
      have : ∀ j : Fin n, G2 0 j.succ = 0 := hT1b
      simp [hf_expand, Fin.sum_univ_succ, Pi.single_apply, Fin.succ_ne_zero, this]
    have hright : ∀ u : Fin n → R, hf G2 (Fin.cons 0 u) (Pi.single 0 1) = 0 := by
      intro u
      have : ∀ j : Fin n, G2 j.succ 0 = 0 := hT1a
      simp [hf_expand, Fin.sum_univ_succ, Pi.single_apply, Fin.succ_ne_zero, this]
    refine ⟨D * (T1 * B⁻¹), ?_, ?_⟩
    · rw [Matrix.det_mul, Matrix.det_mul, hDdet]
      exact hT3.mul (hT1.mul hBi)
    · have heq : D * (T1 * B⁻¹) * G * (D * (T1 * B⁻¹))ᴴ = D * G2 * Dᴴ := by
        simp only [hG2, hG1, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [heq]
      intro i j hij
      rw [mul_conj_apply]
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j' => rw [hD0, hDs, hleft]
      | succ i' =>
        induction j using Fin.cases with
        | zero => rw [hD0, hDs, hright]
        | succ j' =>
          rw [hDs, hDs, hcons, ← mul_conj_apply]
          exact hT3d (fun h => hij (by rw [h]))

/- English proof (translation)
Introduce `E _ _ _ bar hbar hunr m hm`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hfix : ∀ r : 𝓞 (maximalRealSubfield E), bar (algebraMap _ (𝓞 E) r) = algebraMap _ (𝓞 E) r`. Introduce `r`.

Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Establish `h1 : ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r : 𝓞 E) : E) = algebraMap (maximalRealSubfield E) E (r : maximalRealSubfield E)`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) E]`. Both sides reduce to the same expression. Use `show ((bar _ : 𝓞 E) : E) = ((algebraMap _ (𝓞 E) r : 𝓞 E) : E)`.

Rewrite using `[hbar, h1]`. Conclude with `IsCMField.complexConj_apply_eq_self E _`. Set `σ : 𝓞 E →ₐ[𝓞 (maximalRealSubfield E)] 𝓞 E` to `{ (bar : 𝓞 E →+* 𝓞 E) with commutes' := hfix }`. Establish `hσ : AlgHom.id (𝓞 (maximalRealSubfield E)) (𝓞 E) = σ`. Use `Algebra.FormallyUnramified.ext_of_iInf (I := m) (Ideal.iInf_pow_eq_bot_of_isDomain m hm.ne_top) ?_` and prove the remaining obligations.

Introduce `x`. Rewrite using `[Ideal.Quotient.eq]`. Conclude with `hcon x`. Apply `IsCMField.complexConj_ne_one E` to reduce the goal to its premises. Establish `hring : (IsCMField.complexConj E : E →+* E).comp (algebraMap (𝓞 E) E) = (RingHom.id E).comp (algebraMap (𝓞 E) E)`.

Use extensionality with `x`. Establish `hx : bar x = x` using `(AlgHom.congr_fun hσ x).symm`. Use `show IsCMField.complexConj E (x : E) = (x : E)`. Rewrite using `[← hbar, hx]`. Establish `h2` using `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) hring`.

Use extensionality with `y`. Conclude with `RingHom.congr_fun h2 y`.
-/
theorem PositivityTheory.Xgf.exists_not_mem_sub_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ m : Ideal (𝓞 E), m.IsMaximal → ∃ a : 𝓞 E, a - bar a ∉ m := by
  intro E _ _ _ bar hbar hunr m hm
  by_contra hcon
  push_neg at hcon
  have hfix : ∀ r : 𝓞 (maximalRealSubfield E),
      bar (algebraMap _ (𝓞 E) r) = algebraMap _ (𝓞 E) r := by
    intro r
    apply RingOfIntegers.coe_injective
    have h1 : ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r : 𝓞 E) : E) =
        algebraMap (maximalRealSubfield E) E (r : maximalRealSubfield E) := by
      rw [← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) E]
      rfl
    show ((bar _ : 𝓞 E) : E) = ((algebraMap _ (𝓞 E) r : 𝓞 E) : E)
    rw [hbar, h1]
    exact IsCMField.complexConj_apply_eq_self E _
  let σ : 𝓞 E →ₐ[𝓞 (maximalRealSubfield E)] 𝓞 E :=
    { (bar : 𝓞 E →+* 𝓞 E) with commutes' := hfix }
  have hσ : AlgHom.id (𝓞 (maximalRealSubfield E)) (𝓞 E) = σ := by
    refine Algebra.FormallyUnramified.ext_of_iInf (I := m) (Ideal.iInf_pow_eq_bot_of_isDomain m hm.ne_top) ?_
    intro x
    rw [Ideal.Quotient.eq]
    exact hcon x
  apply IsCMField.complexConj_ne_one E
  have hring : (IsCMField.complexConj E : E →+* E).comp (algebraMap (𝓞 E) E) =
      (RingHom.id E).comp (algebraMap (𝓞 E) E) := by
    ext x
    have hx : bar x = x := (AlgHom.congr_fun hσ x).symm
    show IsCMField.complexConj E (x : E) = (x : E)
    rw [← hbar, hx]
  have h2 := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) hring
  ext y
  exact RingHom.congr_fun h2 y

namespace PositivityTheory.Xgf.LocGen

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[NumberField.isUnit_iff_norm]`. Establish `h1 : ((RingOfIntegers.norm ℚ ((p : ℕ) : 𝓞 F) : 𝓞 ℚ) : ℚ) = ((p : ℕ) : ℚ) ^ Module.finrank ℚ F`. Rewrite using `[RingOfIntegers.coe_norm]`. Establish `: (((p : ℕ) : 𝓞 F) : F) = algebraMap ℚ F ((p : ℕ) : ℚ)` using `by simp`.

Rewrite using `[this, Algebra.norm_algebraMap]`. Rewrite `h` using `[h1, abs_pow, pow_eq_one_iff_of_nonneg (abs_nonneg _) Module.finrank_pos.ne']`. Establish `h2 : (1 : ℚ) < |((p : ℕ) : ℚ)|`. Rewrite using `[Nat.abs_cast]`. Conclude with `p.2.one_lt` after adjusting the coercions.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem natCast_not_unit (F : Type) [Field F] [NumberField F] (p : Nat.Primes) : ¬ IsUnit ((p : ℕ) : 𝓞 F) := by
  intro h
  rw [NumberField.isUnit_iff_norm] at h
  have h1 : ((RingOfIntegers.norm ℚ ((p : ℕ) : 𝓞 F) : 𝓞 ℚ) : ℚ) = ((p : ℕ) : ℚ) ^ Module.finrank ℚ F := by
    rw [RingOfIntegers.coe_norm]
    have : (((p : ℕ) : 𝓞 F) : F) = algebraMap ℚ F ((p : ℕ) : ℚ) := by simp
    rw [this, Algebra.norm_algebraMap]
  rw [h1, abs_pow, pow_eq_one_iff_of_nonneg (abs_nonneg _) Module.finrank_pos.ne'] at h
  have h2 : (1 : ℚ) < |((p : ℕ) : ℚ)| := by
    rw [Nat.abs_cast]
    exact_mod_cast p.2.one_lt
  linarith

/- English proof (translation)
Establish `h : ((n : ℚ_[(p : ℕ)]) : ℂ_[(p : ℕ)]) = (n : ℂ_[(p : ℕ)])` using `by push_cast; rfl`. Rewrite using `[← h, PadicComplex.norm_extends', Padic.norm_natCast_eq_one_iff]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd p.2).2 hn`.
-/
theorem norm_natCast_cp (p : Nat.Primes) (n : ℕ) (hn : ¬ (p : ℕ) ∣ n) : ‖(n : ℂ_[p])‖ = 1 := by
  have h : ((n : ℚ_[(p : ℕ)]) : ℂ_[(p : ℕ)]) = (n : ℂ_[(p : ℕ)]) := by push_cast; rfl
  rw [← h, PadicComplex.norm_extends', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd p.2).2 hn

end PositivityTheory.Xgf.LocGen

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Rewrite `hf` using `[hmon.as_sum]`. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C, Int.coe_castRingHom] at hf`. Establish `hd : f.natDegree ≠ 0`.

Introduce `h0`. Rewrite `hf` using `[h0]`. Simplify using `at hf`. Establish `h1 : y ^ f.natDegree = -∑ i ∈ Finset.range f.natDegree, ((f.coeff i : ℤ) : ℂ_[(p : ℕ)]) * y ^ i` using `eq_neg_of_add_eq_zero_left hf`. Establish `h2 : ‖∑ i ∈ Finset.range f.natDegree, ((f.coeff i : ℤ) : ℂ_[(p : ℕ)]) * y ^ i‖ ≤ ‖y‖ ^ (f.natDegree - 1)`.

Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)` to reduce the goal to its premises. Introduce `i hi`. Rewrite using `[norm_mul, norm_pow]`. Establish `hc : ‖((f.coeff i : ℤ) : ℂ_[(p : ℕ)])‖ ≤ 1` using `IsUltrametricDist.norm_intCast_le_one _ _`. Establish `hi' : i ≤ f.natDegree - 1`.

Use `Finset.mem_range.1 hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Rewrite `h2` using `[← norm_neg, ← h1, norm_pow]`. Establish `h3 : ‖y‖ ^ (f.natDegree - 1) < ‖y‖ ^ f.natDegree` using `pow_lt_pow_right₀ hlt (by omega)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem norm_le_one_lemma (p : Nat.Primes) (y : ℂ_[(p : ℕ)]) (f : Polynomial ℤ) (hmon : f.Monic)
    (hf : f.eval₂ (Int.castRingHom ℂ_[(p : ℕ)]) y = 0) : ‖y‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  rw [hmon.as_sum] at hf
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Int.coe_castRingHom] at hf
  have hd : f.natDegree ≠ 0 := by
    intro h0
    rw [h0] at hf
    simp at hf
  have h1 : y ^ f.natDegree = -∑ i ∈ Finset.range f.natDegree, ((f.coeff i : ℤ) : ℂ_[(p : ℕ)]) * y ^ i :=
    eq_neg_of_add_eq_zero_left hf
  have h2 : ‖∑ i ∈ Finset.range f.natDegree, ((f.coeff i : ℤ) : ℂ_[(p : ℕ)]) * y ^ i‖ ≤
      ‖y‖ ^ (f.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    have hc : ‖((f.coeff i : ℤ) : ℂ_[(p : ℕ)])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
    have hi' : i ≤ f.natDegree - 1 := by
      have := Finset.mem_range.1 hi
      omega
    calc ‖((f.coeff i : ℤ) : ℂ_[(p : ℕ)])‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (f.natDegree - 1) :=
          mul_le_mul hc (pow_le_pow_right₀ hlt.le hi') (by positivity) zero_le_one
      _ = _ := one_mul _
  rw [← norm_neg, ← h1, norm_pow] at h2
  have h3 : ‖y‖ ^ (f.natDegree - 1) < ‖y‖ ^ f.natDegree := pow_lt_pow_right₀ hlt (by omega)
  linarith

open PositivityTheory.Xgf.LocGen in
/- English proof (translation)
Introduce `F _ _ I p hI`. Establish `hpI : Ideal.span {((p : ℕ) : 𝓞 F)} * I ≤ I` using `Ideal.mul_le_right`. Establish `hp0 : ((p : ℕ) : 𝓞 F) ≠ 0` using `by exact_mod_cast p.2.ne_zero`. Establish `hne : Ideal.span {((p : ℕ) : 𝓞 F)} * I ≠ 0`. Use `mul_ne_zero ?_ hI` and prove the remaining obligations.

Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis. Take `⟨δ, hδ⟩` from `IsDedekindDomain.exists_sup_span_eq hpI hne`. Establish `hδI : δ ∈ I` using `hδ ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self δ)`. Establish `hδ0 : δ ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hδ` using `[Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq]`. Establish `h2 : Ideal.span {((p : ℕ) : 𝓞 F)} * I = ⊤ * I` using `by rw [hδ, Ideal.top_mul]`. Establish `h3 : Ideal.span {((p : ℕ) : 𝓞 F)} = ⊤` using `mul_right_cancel₀ hI h2`. Conclude with `natCast_not_unit F p (Ideal.span_singleton_eq_top.1 h3)`. Establish `happrox : ∀ k : ℕ, ∀ x ∈ I, ∃ y ∈ I, x - ((p : ℕ) : 𝓞 F) ^ k * y ∈ Ideal.span {δ}`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `x hx`. Conclude with `⟨x, hx, by simp⟩`.

Consider the case `succ k ih`. Introduce `x hx`. Take `⟨y, hy, hxy⟩` from `ih x hx`. Rewrite `hy` using `[← hδ]`. Take `⟨u, hu, v, hv, rfl⟩` from `Submodule.mem_sup.1 hy`.

Take `⟨z, hz, rfl⟩` from `Ideal.mem_span_singleton_mul.1 hu`. Use `⟨z, hz, ?_⟩` and prove the remaining obligations. Establish `e : x - ((p : ℕ) : 𝓞 F) ^ (k + 1) * z = (x - ((p : ℕ) : 𝓞 F) ^ k * (((p : ℕ) : 𝓞 F) * z + v)) + ((p : ℕ) : 𝓞 F) ^ k * v` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ hxy (Ideal.mul_mem_left _ _ hv)`.

Use `set N := Ideal.absNorm (Ideal.span {δ}) with hN`. Establish `hN0 : N ≠ 0`. Rewrite using `[hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hδ0`. Use `set e := N.factorization (p : ℕ)`.

Use `set n := N / (p : ℕ) ^ e`. Establish `hn : ¬ (p : ℕ) ∣ n` using `Nat.not_dvd_ordCompl p.2 hN0`. Establish `hNmem : (N : 𝓞 F) ∈ Ideal.span {δ}` using `Ideal.absNorm_mem _`. Establish `hmul : ∀ a ∈ I, (n : 𝓞 F) * a ∈ Ideal.span {δ}`. Introduce `a ha`.

Take `⟨y, hy, hay⟩` from `happrox e a ha`. Establish `hNe : ((p : ℕ) : 𝓞 F) ^ e * (n : 𝓞 F) = (N : 𝓞 F)`. Conclude with `Nat.ordProj_mul_ordCompl_eq_self N p` after adjusting the coercions. Establish `e2 : (n : 𝓞 F) * a = (n : 𝓞 F) * (a - ((p : ℕ) : 𝓞 F) ^ e * y) + (N : 𝓞 F) * y`. Rewrite using `[← hNe]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hay) (Ideal.mul_mem_right _ _ hNmem)`. Use `⟨δ, hδI, hδ0, ⟨n, hn, hmul⟩, ?_⟩` and prove the remaining obligations. Introduce `j`.

Establish `hint : ∀ b : 𝓞 F, ‖j (algebraMap (𝓞 F) F b)‖ ≤ 1`. Introduce `b`. Take `⟨f, hmon, hf⟩` from `NumberField.RingOfIntegers.isIntegral_coe b`. Use `norm_le_one_lemma p _ f hmon ?_` and prove the remaining obligations. Establish `h` using `congrArg j hf`.

Rewrite `h` using `[Polynomial.hom_eval₂, map_zero]`. Rewrite `h` using `[show j.comp (algebraMap ℤ F) = Int.castRingHom _ from RingHom.ext_int _ _]`. Then use the resulting hypothesis. Establish `bound : ∀ a ∈ I, ‖j (algebraMap (𝓞 F) F a)‖ ≤ ‖j (algebraMap (𝓞 F) F δ)‖`. Introduce `a ha`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 (hmul a ha)`.

Establish `h1 : j (algebraMap (𝓞 F) F b) * j (algebraMap (𝓞 F) F δ) = (n : ℂ_[(p : ℕ)]) * j (algebraMap (𝓞 F) F a)`. Use `congrArg (fun t : 𝓞 F => j (algebraMap (𝓞 F) F t)) hb` as an intermediate fact. Simplify `this` using `only [map_mul, map_natCast]`. Establish `h2 : ‖j (algebraMap (𝓞 F) F a)‖ = ‖j (algebraMap (𝓞 F) F b)‖ * ‖j (algebraMap (𝓞 F) F δ)‖`. Use `congrArg norm h1` as an intermediate fact.

Rewrite `this` using `[norm_mul, norm_mul, norm_natCast_cp p n hn, one_mul]`. Conclude with `this.symm`. Rewrite using `[h2]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hint b)`. Establish `hsup : (⨆ a : I, ‖(j.comp (algebraMap (𝓞 F) F)) a‖) = ‖j (algebraMap (𝓞 F) F δ)‖`.

Apply `le_antisymm` to reduce the goal to its premises. Conclude with `ciSup_le fun a => bound a a.2`. Use `le_ciSup (f := fun a : I => ‖(j.comp (algebraMap (𝓞 F) F)) a‖) ?_ ⟨δ, hδI⟩` and prove the remaining obligations. Use `⟨‖j (algebraMap (𝓞 F) F δ)‖, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`.

Conclude with `bound a a.2`. Rewrite using `[logIdeal, hsup]`.
-/
theorem PositivityTheory.Xgf.ideal_padic_generator_log_norm : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)) (p : Nat.Primes), I ≠ ⊥ → ∃ δ ∈ I, δ ≠ 0 ∧ (∃ n : ℕ, ¬ (p : ℕ) ∣ n ∧ ∀ a ∈ I, (n : 𝓞 F) * a ∈ Ideal.span {δ}) ∧ ∀ j : F →+* ℂ_[p], Real.log ‖j (δ : F)‖ = logIdeal (j.comp (algebraMap (𝓞 F) F)) I := by
  intro F _ _ I p hI
  have hpI : Ideal.span {((p : ℕ) : 𝓞 F)} * I ≤ I := Ideal.mul_le_right
  have hp0 : ((p : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hne : Ideal.span {((p : ℕ) : 𝓞 F)} * I ≠ 0 := by
    refine mul_ne_zero ?_ hI
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  obtain ⟨δ, hδ⟩ := IsDedekindDomain.exists_sup_span_eq hpI hne
  have hδI : δ ∈ I := hδ ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self δ)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq] at hδ
    have h2 : Ideal.span {((p : ℕ) : 𝓞 F)} * I = ⊤ * I := by rw [hδ, Ideal.top_mul]
    have h3 : Ideal.span {((p : ℕ) : 𝓞 F)} = ⊤ := mul_right_cancel₀ hI h2
    exact natCast_not_unit F p (Ideal.span_singleton_eq_top.1 h3)
  have happrox : ∀ k : ℕ, ∀ x ∈ I, ∃ y ∈ I, x - ((p : ℕ) : 𝓞 F) ^ k * y ∈ Ideal.span {δ} := by
    intro k
    induction k with
    | zero =>
      intro x hx
      exact ⟨x, hx, by simp⟩
    | succ k ih =>
      intro x hx
      obtain ⟨y, hy, hxy⟩ := ih x hx
      rw [← hδ] at hy
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨z, hz, rfl⟩ := Ideal.mem_span_singleton_mul.1 hu
      refine ⟨z, hz, ?_⟩
      have e : x - ((p : ℕ) : 𝓞 F) ^ (k + 1) * z =
          (x - ((p : ℕ) : 𝓞 F) ^ k * (((p : ℕ) : 𝓞 F) * z + v)) + ((p : ℕ) : 𝓞 F) ^ k * v := by ring
      rw [e]
      exact Ideal.add_mem _ hxy (Ideal.mul_mem_left _ _ hv)
  set N := Ideal.absNorm (Ideal.span {δ}) with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hδ0
  set e := N.factorization (p : ℕ)
  set n := N / (p : ℕ) ^ e
  have hn : ¬ (p : ℕ) ∣ n := Nat.not_dvd_ordCompl p.2 hN0
  have hNmem : (N : 𝓞 F) ∈ Ideal.span {δ} := Ideal.absNorm_mem _
  have hmul : ∀ a ∈ I, (n : 𝓞 F) * a ∈ Ideal.span {δ} := by
    intro a ha
    obtain ⟨y, hy, hay⟩ := happrox e a ha
    have hNe : ((p : ℕ) : 𝓞 F) ^ e * (n : 𝓞 F) = (N : 𝓞 F) := by
      exact_mod_cast Nat.ordProj_mul_ordCompl_eq_self N p
    have e2 : (n : 𝓞 F) * a = (n : 𝓞 F) * (a - ((p : ℕ) : 𝓞 F) ^ e * y) + (N : 𝓞 F) * y := by
      rw [← hNe]
      ring
    rw [e2]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hay) (Ideal.mul_mem_right _ _ hNmem)
  refine ⟨δ, hδI, hδ0, ⟨n, hn, hmul⟩, ?_⟩
  intro j
  have hint : ∀ b : 𝓞 F, ‖j (algebraMap (𝓞 F) F b)‖ ≤ 1 := by
    intro b
    obtain ⟨f, hmon, hf⟩ := NumberField.RingOfIntegers.isIntegral_coe b
    refine norm_le_one_lemma p _ f hmon ?_
    have h := congrArg j hf
    rw [Polynomial.hom_eval₂, map_zero] at h
    rwa [show j.comp (algebraMap ℤ F) = Int.castRingHom _ from RingHom.ext_int _ _] at h
  have bound : ∀ a ∈ I, ‖j (algebraMap (𝓞 F) F a)‖ ≤ ‖j (algebraMap (𝓞 F) F δ)‖ := by
    intro a ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hmul a ha)
    have h1 : j (algebraMap (𝓞 F) F b) * j (algebraMap (𝓞 F) F δ) =
        (n : ℂ_[(p : ℕ)]) * j (algebraMap (𝓞 F) F a) := by
      have := congrArg (fun t : 𝓞 F => j (algebraMap (𝓞 F) F t)) hb
      simpa only [map_mul, map_natCast] using this
    have h2 : ‖j (algebraMap (𝓞 F) F a)‖ = ‖j (algebraMap (𝓞 F) F b)‖ * ‖j (algebraMap (𝓞 F) F δ)‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_mul, norm_natCast_cp p n hn, one_mul] at this
      exact this.symm
    rw [h2]
    exact mul_le_of_le_one_left (norm_nonneg _) (hint b)
  have hsup : (⨆ a : I, ‖(j.comp (algebraMap (𝓞 F) F)) a‖) = ‖j (algebraMap (𝓞 F) F δ)‖ := by
    apply le_antisymm
    · exact ciSup_le fun a => bound a a.2
    · refine le_ciSup (f := fun a : I => ‖(j.comp (algebraMap (𝓞 F) F)) a‖) ?_ ⟨δ, hδI⟩
      refine ⟨‖j (algebraMap (𝓞 F) F δ)‖, ?_⟩
      rintro _ ⟨a, rfl⟩
      exact bound a a.2
  rw [logIdeal, hsup]
