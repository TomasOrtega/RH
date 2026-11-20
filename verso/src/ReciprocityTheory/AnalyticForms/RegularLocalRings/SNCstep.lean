import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsAtlas

namespace ReciprocityTheory.AnForm.R

open MvPolynomial ReciprocityTheory.AnForm.M

section SlopeTestRemainingChoices

variable {n : ℕ}

/- English proof (translation)
Proceed by induction on `φ using MvPolynomial.induction_on`. Simplify using the standard rewrite rules. Simplify using `[*]`. Simplify using `[*]`.
-/
theorem eval_bind_one {m : ℕ} (y : Fin m → ℂ) {τ : Type} (g : τ → MvPolynomial (Fin m) ℂ)
    (φ : MvPolynomial τ ℂ) : eval y (bind₁ g φ) = eval (fun q => eval y (g q)) φ := by
  induction φ using MvPolynomial.induction_on
  · simp
  · simp [*]
  · simp [*]

noncomputable def locEvalPt (I : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ g ∈ I, eval p g = 0) : locRing I p →+* ℂ :=
  Ideal.Quotient.lift _
    (IsLocalization.lift (M := (ptIdeal p).primeCompl) (S := locPt p) (g := eval p)
      (fun y => by
        have hy : (y : MvPolynomial (Fin n) ℂ) ∉ ptIdeal p := y.2
        exact isUnit_iff_ne_zero.2 fun h => hy (RingHom.mem_ker.2 h)))
    (by
      intro z hz
      have hle : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) I ≤
          RingHom.ker (IsLocalization.lift (M := (ptIdeal p).primeCompl) (S := locPt p)
            (g := eval p) (fun y => by
              have hy : (y : MvPolynomial (Fin n) ℂ) ∉ ptIdeal p := y.2
              exact isUnit_iff_ne_zero.2 fun h => hy (RingHom.mem_ker.2 h))) := by
        rw [Ideal.map_le_iff_le_comap]
        intro g hg
        simp only [Ideal.mem_comap, RingHom.mem_ker, IsLocalization.lift_eq]
        exact hp g hg
      exact hle hz)

/- English proof (translation)
Conclude with `IsLocalization.lift_eq _ g`.
-/
theorem locEvalPt_algebraMap (I : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ g ∈ I, eval p g = 0) (g : MvPolynomial (Fin n) ℂ) :
    locEvalPt I p hp (Ideal.Quotient.mk _ (algebraMap _ (locPt p) g)) = eval p g := by
  exact IsLocalization.lift_eq _ g

/- English proof (translation)
Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective u`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (ptIdeal p).primeCompl z`. Establish `hs : eval p (s : MvPolynomial (Fin n) ℂ) ≠ 0` using `fun h0 => s.2 (RingHom.mem_ker.2 h0)`. Establish `key : ∀ x : MvPolynomial (Fin n) ℂ, algebraMap _ (locRing I p) x = Ideal.Quotient.mk _ (algebraMap _ (locPt p) x)` using `fun x => by rw [Ideal.Quotient.mk_algebraMap]`. Establish `hspec : IsLocalization.mk' (locPt p) a s * algebraMap _ (locPt p) (s : MvPolynomial (Fin n) ℂ) = algebraMap _ (locPt p) a` using `IsLocalization.mk'_spec _ _ _`.

Establish `ha : eval p a ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg (locEvalPt I p hp) (congrArg (Ideal.Quotient.mk (Ideal.map (algebraMap _ (locPt p)) I)) hspec)`. Rewrite `h1` using `[map_mul, map_mul, locEvalPt_algebraMap, locEvalPt_algebraMap, h0]`. Conclude with `(hu.map (locEvalPt I p hp)).ne_zero (by simpa [hs] using h1)`.

Rewrite `h` using `[key, key]`. Establish `hmem : algebraMap _ (locPt p) ((s : MvPolynomial (Fin n) ℂ) * F - a * G) ∈ Ideal.map (algebraMap _ (locPt p)) I`. Establish `h2` using `Ideal.Quotient.eq.1 (h.trans (map_mul _ _ _).symm)`. Establish `h3` using `Ideal.mul_mem_left _ (algebraMap _ (locPt p) (s : MvPolynomial (Fin n) ℂ)) h2`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_sub, map_mul, map_mul, ← hspec]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨m, hm, hmI⟩` from `(IsLocalization.algebraMap_mem_map_algebraMap_iff (ptIdeal p).primeCompl (locPt p) I _).1 hmem`. Conclude with `⟨a, s, m, ha, hs, fun h0 => hm (RingHom.mem_ker.2 h0), hmI⟩`.
-/
theorem exists_poly_of_locRing_eq (I : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ g ∈ I, eval p g = 0) (F G : MvPolynomial (Fin n) ℂ) (u : locRing I p) (hu : IsUnit u)
    (h : algebraMap _ (locRing I p) F = u * algebraMap _ (locRing I p) G) :
    ∃ a b c : MvPolynomial (Fin n) ℂ, eval p a ≠ 0 ∧ eval p b ≠ 0 ∧ eval p c ≠ 0 ∧
      c * (b * F - a * G) ∈ I := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (ptIdeal p).primeCompl z
  have hs : eval p (s : MvPolynomial (Fin n) ℂ) ≠ 0 := fun h0 => s.2 (RingHom.mem_ker.2 h0)
  have key : ∀ x : MvPolynomial (Fin n) ℂ, algebraMap _ (locRing I p) x =
      Ideal.Quotient.mk _ (algebraMap _ (locPt p) x) := fun x => by rw [Ideal.Quotient.mk_algebraMap]
  have hspec : IsLocalization.mk' (locPt p) a s * algebraMap _ (locPt p) (s : MvPolynomial (Fin n) ℂ) =
      algebraMap _ (locPt p) a := IsLocalization.mk'_spec _ _ _
  have ha : eval p a ≠ 0 := by
    intro h0
    have h1 := congrArg (locEvalPt I p hp)
      (congrArg (Ideal.Quotient.mk (Ideal.map (algebraMap _ (locPt p)) I)) hspec)
    rw [map_mul, map_mul, locEvalPt_algebraMap, locEvalPt_algebraMap, h0] at h1
    exact (hu.map (locEvalPt I p hp)).ne_zero (by simpa [hs] using h1)
  rw [key, key] at h
  have hmem : algebraMap _ (locPt p) ((s : MvPolynomial (Fin n) ℂ) * F - a * G) ∈
      Ideal.map (algebraMap _ (locPt p)) I := by
    have h2 := Ideal.Quotient.eq.1 (h.trans (map_mul _ _ _).symm)
    have h3 := Ideal.mul_mem_left _ (algebraMap _ (locPt p) (s : MvPolynomial (Fin n) ℂ)) h2
    convert h3 using 1
    rw [map_sub, map_mul, map_mul, ← hspec]
    ring
  obtain ⟨m, hm, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (ptIdeal p).primeCompl (locPt p) I _).1 hmem
  exact ⟨a, s, m, ha, hs, fun h0 => hm (RingHom.mem_ker.2 h0), hmI⟩

/- English proof (translation)
Establish `hL : ∀ l, w l ^ (σ l).elim 0 m = ∏ k, if σ l = some k then w l ^ m k else 1`. Introduce `l`. Consider the cases of `h : σ l with`. Consider the case `none => simp`. Consider the case `some k0 => simp [Finset.prod_ite_eq, Finset.prod_ite_eq']`.

Establish `hR : ∀ k, Option.elim (σ' k) 1 (fun i => w i ^ m k) = ∏ l ∈ J, if σ l = some k then w l ^ m k else 1`. Introduce `k`. Consider the cases of `h : σ' k with`. Consider the case `none`. Simplify using `only [Option.elim]`.

Use `(Finset.prod_eq_one fun l _ => ?_).symm` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce `hl`. Rewrite `hl` using `[← hσ', h]`. Consider the cases of `hl`.

Consider the case `some l0`. Establish `hl0 : σ l0 = some k` using `(hσ' k l0).1 h`. Establish `hJ : l0 ∈ J`. Assume the negation of the conclusion as `hn`. Rewrite `hl0` using `[(hnone l0).2 hn]`.

Consider the cases of `hl0`. Simplify using `only [Option.elim]`. Rewrite using `[Finset.prod_eq_single l0]`. Rewrite using `[if_pos hl0]`. Introduce `l _ hne`.

Rewrite using `[if_neg]`. Introduce `hl`. Rewrite `hl` using `[← hσ', h]`. Conclude with `hne (Option.some_injective _ hl).symm`. Introduce `hn`.

Conclude with `absurd hJ hn`. Rewrite using `[Finset.prod_congr rfl fun l _ => hL l, Finset.prod_comm]`. Conclude with `Finset.prod_congr rfl fun k _ => (hR k).symm`.
-/
theorem prod_reindex_option {e rc : ℕ} (J : Finset (Fin e)) (σ : Fin e → Option (Fin rc))
    (hnone : ∀ l, σ l = none ↔ l ∉ J) (σ' : Fin rc → Option (Fin e))
    (hσ' : ∀ k l, σ' k = some l ↔ σ l = some k) (m : Fin rc → ℕ) (w : Fin e → ℂ) :
    ∏ l ∈ J, w l ^ (σ l).elim 0 m = ∏ k, Option.elim (σ' k) 1 (fun i => w i ^ m k) := by
  have hL : ∀ l, w l ^ (σ l).elim 0 m = ∏ k, if σ l = some k then w l ^ m k else 1 := by
    intro l
    cases h : σ l with
    | none => simp
    | some k0 => simp [Finset.prod_ite_eq, Finset.prod_ite_eq']
  have hR : ∀ k, Option.elim (σ' k) 1 (fun i => w i ^ m k) =
      ∏ l ∈ J, if σ l = some k then w l ^ m k else 1 := by
    intro k
    cases h : σ' k with
    | none =>
      simp only [Option.elim]
      refine (Finset.prod_eq_one fun l _ => ?_).symm
      rw [if_neg]
      intro hl
      rw [← hσ', h] at hl
      cases hl
    | some l0 =>
      have hl0 : σ l0 = some k := (hσ' k l0).1 h
      have hJ : l0 ∈ J := by
        by_contra hn
        rw [(hnone l0).2 hn] at hl0
        cases hl0
      simp only [Option.elim]
      rw [Finset.prod_eq_single l0]
      · rw [if_pos hl0]
      · intro l _ hne
        rw [if_neg]
        intro hl
        rw [← hσ', h] at hl
        exact hne (Option.some_injective _ hl).symm
      · intro hn
        exact absurd hJ hn
  rw [Finset.prod_congr rfl fun l _ => hL l, Finset.prod_comm]
  exact Finset.prod_congr rfl fun k _ => (hR k).symm

end SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `hc : Continuous fun y : R.src i => R.coord i y` using `(R.isEmbedding i).continuous`. Establish `ho : IsOpen ((fun y : R.src i => R.coord i y) ⁻¹' {v | eval v g ≠ 0})` using `(isOpen_ne_fun (MvPolynomial.continuous_eval g) continuous_const).preimage hc`. Establish `h2` using `(R.isOpen_alt_bis i).isOpenMap_subtype_val _ ho`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`.

Simplify using `[and_comm]`.
-/
theorem AlgRes.isOpen_nonvan {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (i : Fin R.n) (g : MvPolynomial (Fin (R.amb i)) ℂ) :
    IsOpen {y | y ∈ R.src i ∧ eval (R.coord i y) g ≠ 0} := by
  have hc : Continuous fun y : R.src i => R.coord i y := (R.isEmbedding i).continuous
  have ho : IsOpen ((fun y : R.src i => R.coord i y) ⁻¹' {v | eval v g ≠ 0}) :=
    (isOpen_ne_fun (MvPolynomial.continuous_eval g) continuous_const).preimage hc
  have h2 := (R.isOpen_alt_bis i).isOpenMap_subtype_val _ ho
  convert h2 using 1
  ext y
  simp [and_comm]

/- English proof (translation)
Establish `h : R.coord i x ∈ R.coord i '' R.src i` using `⟨x, hx, rfl⟩`. Rewrite `h` using `[R.image i]`. Conclude with `h`.
-/
theorem AlgRes.coord_mem_zero {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (i : Fin R.n) {x : R.M} (hx : x ∈ R.src i) :
    ∀ g ∈ R.ideal i, eval (R.coord i x) g = 0 := by
  have h : R.coord i x ∈ R.coord i '' R.src i := ⟨x, hx, rfl⟩
  rw [R.image i] at h
  exact h

/- English proof (translation)
Take `⟨m, hm⟩` from `R.mult f a hf hfP hz`. Use `⟨m, fun x => ?_⟩` and prove the remaining obligations. Establish `hx : x ∈ R.src (idx x)` using `hidx x`. Take `⟨u, hu, hfu⟩` from `hm (idx x) x hx`. Take `⟨pa, pb, pc, ha, hb, hc, hI⟩` from `exists_poly_of_locRing_eq _ _ (R.coord_mem_zero _ hx) _ (∏ l ∈ (R.sncAt (idx x) x hx).J, (R.sncAt (idx x) x hx).r l ^ ((R.sncAt (idx x) x hx).σ l).elim 0 m) u hu (by rw [hfu, map_prod]; simp only [map_pow])`.

Take `⟨O, hOo, hxO, -, hOc⟩` from `R.comp_eq (idx x) x hx`. Use `set d := R.sncAt (idx x) x hx with hd`. Establish `hO' : IsOpen (O ∩ ({y | y ∈ R.src (idx x) ∧ eval (R.coord (idx x) y) pa ≠ 0} ∩ {y | y ∈ R.src (idx x) ∧ eval (R.coord (idx x) y) pb ≠ 0} ∩ {y | y ∈ R.src (idx x) ∧ eval (R.coord (idx x) y) pc ≠ 0}))` using `hOo.inter (((R.isOpen_nonvan _ pa).inter (R.isOpen_nonvan _ pb)).inter (R.isOpen_nonvan _ pc))`. Take `⟨ψ, hψc, hxψ, hψs, hψe⟩` from `hA.2 (idx x) x hx d.r d.span_eq _ hO' ⟨hxO, ⟨⟨hx, ha⟩, ⟨hx, hb⟩⟩, ⟨hx, hc⟩⟩`. Establish `hJ : ∀ l k, d.σ l = some k → l ∈ d.J`.

Introduce `l k hl`. Assume the negation of the conclusion as `hJ`. Rewrite `hl` using `[(d.σ_eq_none l).2 hJ]`. Consider the cases of `hl`. Set `σ' : Fin R.rc → Option (Fin e)` to `fun k => if h : ∃ l, d.σ l = some k then some (Classical.choose h) else none`.

Establish `hσ' : ∀ k l, σ' k = some l ↔ d.σ l = some k`. Introduce `k l`. Distinguish the cases in `h : ∃ l, d.σ l = some k`. Establish `hc0` using `Classical.choose_spec h`. Simplify using `only [σ', dif_pos h, Option.some.injEq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `hc0`. Introduce `hl`. Conclude with `d.σ_injOn (hJ _ _ hc0) (hJ _ _ hl) (by rw [hc0, hl])`.

Simplify using `only [σ', dif_neg h]`. Prove the components needed by the constructor for the conclusion. Introduce `h'`. Consider the cases of `h'`. Introduce `hl`.

Conclude with `absurd ⟨l, hl⟩ h`. Use `⟨ψ, hψc, hxψ, fun y hy => (hψs hy).2, σ', ?_, ?_, fun y => eval (R.coord (idx x) y) pa / eval (R.coord (idx x) y) pb, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k k' l h1 h2`. Rewrite `h1`, `h2` using `[hσ']`. Rewrite `h2` using `[h1]`.

Conclude with `Option.some.inj h2`. Introduce `k`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hyk, hyψ⟩`.

Establish `hyO : y ∈ R.comp k ∩ O` using `⟨hyk, (hψs hyψ).1.1⟩`. Rewrite `hyO` using `[hOc k]`. Take `⟨-, l, hl, h0⟩` from `hyO`. Use `⟨hyψ, l, (hσ' k l).2 hl, ?_⟩` and prove the remaining obligations. Rewrite using `[hψe y hyψ]`.

Conclude with `h0`. Introduce and unpack `⟨hyψ, l, hl, h0⟩`. Use `⟨?_, hyψ⟩` and prove the remaining obligations. Establish `hyO : y ∈ {y ∈ O | ∃ l, d.σ l = some k ∧ eval (R.coord (idx x) y) (d.r l) = 0}`. Use `⟨(hψs hyψ).1.1, l, (hσ' k l).1 hl, ?_⟩` and prove the remaining obligations.

Rewrite `h0` using `[hψe y hyψ]`. Conclude with `h0`. Rewrite `hyO` using `[← hOc k]`. Conclude with `hyO.1`. Introduce `j z hz`.

Establish `hz' : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.src (idx x)` using `⟨hz.1, (hψs hz.2).2⟩`. Establish `h1` using `hA.1 (idx x) pa j z hz'`. Establish `h2` using `hA.1 (idx x) pb j z hz'`. Conclude with `h1.div h2 (hψs hz.2).1.2.1.2.2`. Introduce `y hy`.

Conclude with `div_ne_zero (hψs hy).1.2.1.1.2 (hψs hy).1.2.1.2.2`. Introduce `y hy`. Establish `hyO` using `(hψs hy).1`. Establish `hyz` using `R.coord_mem_zero (idx x) (hψs hy).2 _ hI`. Establish `hcy : eval (R.coord (idx x) y) pc ≠ 0` using `hyO.2.2.2`.

Establish `hby : eval (R.coord (idx x) y) pb ≠ 0` using `hyO.2.1.2.2`. Simplify using `only [map_mul, map_sub] at hyz`. Establish `hyz'` using `(mul_eq_zero.1 hyz).resolve_left hcy`. Rewrite `hyz'` using `[sub_eq_zero]`. Establish `hF : eval (R.coord (idx x) y) (bind₁ (R.lift (idx x)) f) = eval (R.coord (idx x) y) pa / eval (R.coord (idx x) y) pb * eval (R.coord (idx x) y) (∏ l ∈ d.J, d.r l ^ (d.σ l).elim 0 m)`.

Rewrite using `[div_mul_eq_mul_div, eq_div_iff hby]`. Take the linear combination `hyz'`. Establish `hG : eval (R.coord (idx x) y) (∏ l ∈ d.J, d.r l ^ (d.σ l).elim 0 m) = ∏ k, Option.elim (σ' k) 1 (fun i => eval (R.coord (idx x) y) (d.r i) ^ m k)`. Rewrite using `[map_prod]`. Simplify using `only [map_pow]`.

Conclude with `prod_reindex_option d.J d.σ d.σ_eq_none σ' hσ' m (fun l => eval (R.coord (idx x) y) (d.r l))`. Use `show eval _ f = _`. Rewrite using `[← eval_bind_one, hF, hG]`. Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[hψe y hy]`. Apply the tactic sequence `rcases σ' k with _ | l <;> rfl`.
-/
theorem AlgRes.isSNC_pullback {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (A : FinHolAtlas e R.M) (hA : R.IsGoodAtlas A)
    (idx : R.M → Fin R.n) (hidx : ∀ x, x ∈ R.src (idx x)) (φ : R.M → R.M → ℝ)
    (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (hf : IsMultiHomog f a) (hfP : f ∉ P)
    (hz : ∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D) :
    ∃ m : Fin R.rc → ℕ,
      IsSNC A ⟨fun x => R.src (idx x), fun x => R.isOpen_alt_bis (idx x), hidx, φ⟩
        (fun x y => eval (fun q => eval (R.coord (idx x) y) (R.lift (idx x) q)) f) m R.comp := by
  classical
  obtain ⟨m, hm⟩ := R.mult f a hf hfP hz
  refine ⟨m, fun x => ?_⟩
  have hx : x ∈ R.src (idx x) := hidx x
  obtain ⟨u, hu, hfu⟩ := hm (idx x) x hx
  obtain ⟨pa, pb, pc, ha, hb, hc, hI⟩ := exists_poly_of_locRing_eq _ _ (R.coord_mem_zero _ hx)
    _ (∏ l ∈ (R.sncAt (idx x) x hx).J, (R.sncAt (idx x) x hx).r l ^
      ((R.sncAt (idx x) x hx).σ l).elim 0 m) u hu (by rw [hfu, map_prod]; simp only [map_pow])
  obtain ⟨O, hOo, hxO, -, hOc⟩ := R.comp_eq (idx x) x hx
  set d := R.sncAt (idx x) x hx with hd
  have hO' : IsOpen (O ∩ ({y | y ∈ R.src (idx x) ∧ eval (R.coord (idx x) y) pa ≠ 0} ∩
      {y | y ∈ R.src (idx x) ∧ eval (R.coord (idx x) y) pb ≠ 0} ∩
      {y | y ∈ R.src (idx x) ∧ eval (R.coord (idx x) y) pc ≠ 0})) :=
    hOo.inter (((R.isOpen_nonvan _ pa).inter (R.isOpen_nonvan _ pb)).inter (R.isOpen_nonvan _ pc))
  obtain ⟨ψ, hψc, hxψ, hψs, hψe⟩ := hA.2 (idx x) x hx d.r d.span_eq _ hO'
    ⟨hxO, ⟨⟨hx, ha⟩, ⟨hx, hb⟩⟩, ⟨hx, hc⟩⟩
  have hJ : ∀ l k, d.σ l = some k → l ∈ d.J := by
    intro l k hl; by_contra hJ; rw [(d.σ_eq_none l).2 hJ] at hl; cases hl
  let σ' : Fin R.rc → Option (Fin e) := fun k =>
    if h : ∃ l, d.σ l = some k then some (Classical.choose h) else none
  have hσ' : ∀ k l, σ' k = some l ↔ d.σ l = some k := by
    intro k l
    by_cases h : ∃ l, d.σ l = some k
    · have hc0 := Classical.choose_spec h
      simp only [σ', dif_pos h, Option.some.injEq]
      constructor
      · rintro rfl; exact hc0
      · intro hl
        exact d.σ_injOn (hJ _ _ hc0) (hJ _ _ hl) (by rw [hc0, hl])
    · simp only [σ', dif_neg h]
      constructor
      · intro h'; cases h'
      · intro hl; exact absurd ⟨l, hl⟩ h
  refine ⟨ψ, hψc, hxψ, fun y hy => (hψs hy).2, σ', ?_, ?_,
    fun y => eval (R.coord (idx x) y) pa / eval (R.coord (idx x) y) pb, ?_, ?_, ?_⟩
  · intro k k' l h1 h2
    rw [hσ'] at h1 h2
    rw [h1] at h2
    exact Option.some.inj h2
  · intro k
    ext y
    constructor
    · rintro ⟨hyk, hyψ⟩
      have hyO : y ∈ R.comp k ∩ O := ⟨hyk, (hψs hyψ).1.1⟩
      rw [hOc k] at hyO
      obtain ⟨-, l, hl, h0⟩ := hyO
      refine ⟨hyψ, l, (hσ' k l).2 hl, ?_⟩
      rw [hψe y hyψ]; exact h0
    · rintro ⟨hyψ, l, hl, h0⟩
      refine ⟨?_, hyψ⟩
      have hyO : y ∈ {y ∈ O | ∃ l, d.σ l = some k ∧ eval (R.coord (idx x) y) (d.r l) = 0} := by
        refine ⟨(hψs hyψ).1.1, l, (hσ' k l).1 hl, ?_⟩
        rw [hψe y hyψ] at h0; exact h0
      rw [← hOc k] at hyO
      exact hyO.1
  · intro j z hz
    have hz' : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.src (idx x) :=
      ⟨hz.1, (hψs hz.2).2⟩
    have h1 := hA.1 (idx x) pa j z hz'
    have h2 := hA.1 (idx x) pb j z hz'
    exact h1.div h2 (hψs hz.2).1.2.1.2.2
  · intro y hy
    exact div_ne_zero (hψs hy).1.2.1.1.2 (hψs hy).1.2.1.2.2
  · intro y hy
    have hyO := (hψs hy).1
    have hyz := R.coord_mem_zero (idx x) (hψs hy).2 _ hI
    have hcy : eval (R.coord (idx x) y) pc ≠ 0 := hyO.2.2.2
    have hby : eval (R.coord (idx x) y) pb ≠ 0 := hyO.2.1.2.2
    simp only [map_mul, map_sub] at hyz
    have hyz' := (mul_eq_zero.1 hyz).resolve_left hcy
    rw [sub_eq_zero] at hyz'
    have hF : eval (R.coord (idx x) y) (bind₁ (R.lift (idx x)) f) =
        eval (R.coord (idx x) y) pa / eval (R.coord (idx x) y) pb *
          eval (R.coord (idx x) y) (∏ l ∈ d.J, d.r l ^ (d.σ l).elim 0 m) := by
      rw [div_mul_eq_mul_div, eq_div_iff hby]
      linear_combination hyz'
    have hG : eval (R.coord (idx x) y) (∏ l ∈ d.J, d.r l ^ (d.σ l).elim 0 m) =
        ∏ k, Option.elim (σ' k) 1 (fun i => eval (R.coord (idx x) y) (d.r i) ^ m k) := by
      rw [map_prod]; simp only [map_pow]
      exact prod_reindex_option d.J d.σ d.σ_eq_none σ' hσ' m (fun l => eval (R.coord (idx x) y) (d.r l))
    show eval _ f = _
    rw [← eval_bind_one, hF, hG]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hψe y hy]
    rcases σ' k with _ | l <;> rfl

/- English proof (translation)
Establish `hset : (A.chart j).target ∩ (A.chart j).symm ⁻¹' {x | ∃ i, x ∈ R.src i ∧ (fun q => eval (R.coord i x) (R.lift i q)) ∈ conePts D} = ⋃ i, ((A.chart j).target ∩ (A.chart j).symm ⁻¹' {x | x ∈ R.src i ∧ (fun q => eval (R.coord i x) (R.lift i q)) ∈ conePts D})`. Use extensionality with `y`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, i, h2⟩`.

Conclude with `⟨i, h1, h2⟩`. Introduce and unpack `⟨i, h1, h2⟩`. Conclude with `⟨h1, i, h2⟩`. Establish `hyp : ∀ l : Fin e, MeasureTheory.volume {w : Fin e → ℂ | w l = 0} = 0`. Introduce `l`.

Establish `: {w : Fin e → ℂ | w l = 0} = Set.univ.pi (Function.update (fun _ => (Set.univ : Set ℂ)) l {0})`. Use extensionality with `w`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_univ_pi]`. Prove the components needed by the constructor for the conclusion. Introduce `hw k`.

Distinguish the cases in `hk : k = l`. Substitute `hk` using the available equality. Simplify using `[hw]`. Simplify using `[Function.update_of_ne hk]`. Introduce `hw`.

Simplify using `using hw l`. Rewrite using `[this, MeasureTheory.volume_pi_pi]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ l) (by simp)`. Rewrite using `[hset]`. Use `MeasureTheory.measure_iUnion_null fun i => ?_` and prove the remaining obligations.

Apply `MeasureTheory.measure_null_of_locally_null` to reduce the goal to its premises. Introduce and unpack `y0 ⟨hy0t, hy0s, -⟩`. Take `⟨ψ, hψc, hxψ, hψs, hψe⟩` from `hA.2 i _ hy0s (R.sncAt i _ hy0s).r (R.sncAt i _ hy0s).span_eq _ (R.isOpen_nonvan i (R.sncAt i _ hy0s).h) ⟨hy0s, (R.sncAt i _ hy0s).eval_h⟩`. Use `set d := R.sncAt i _ hy0s with hd`. Establish `hU : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source)` using `(A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target ψ.open_source`.

Use `⟨_, inter_mem_nhdsWithin _ (hU.mem_nhds ⟨hy0t, hxψ⟩), ?_⟩` and prove the remaining obligations. Establish `hN : MeasureTheory.volume ((ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) ∩ {w : Fin e → ℂ | ∏ l ∈ d.J, w l = 0}) = 0`. Use `MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_iUnion_null hyp)` and prove the remaining obligations. Introduce and unpack `w ⟨-, hw⟩`. Take `⟨l, -, hl⟩` from `Finset.prod_eq_zero_iff.1 hw`.

Conclude with `Set.mem_iUnion.2 ⟨l, hl⟩`. Establish `hg : DifferentiableOn ℝ ((A.chart j) ∘ ψ.symm) ((ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) ∩ {w : Fin e → ℂ | ∏ l ∈ d.J, w l = 0})` using `fun w hw => (((hψc j).2 w hw.1).differentiableAt.restrictScalars ℝ).differentiableWithinAt`. Use `MeasureTheory.measure_mono_null ?_ (MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _ hg hN)` and prove the remaining obligations. Introduce and unpack `y ⟨⟨hyt, hys, hyD⟩, -, hyψ⟩`. Use `⟨ψ ((A.chart j).symm y), ⟨⟨ψ.map_source hyψ, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.mem_preimage, ψ.left_inv hyψ]`. Conclude with `(A.chart j).map_target hyt`. Establish `hbd` using `(R.zero_bd i _ hys).2 hyD _ d.mem_bd`. Rewrite `hbd` using `[map_mul, map_prod]`. Establish `h0` using `(mul_eq_zero.1 hbd).resolve_left (hψs hyψ).1.2`.

Simplify using `only [Set.mem_ofPred_eq, hψe _ hyψ]`. Conclude with `h0`. Simplify using `only [Function.comp_apply, ψ.left_inv hyψ, (A.chart j).right_inv hyt]`.
-/
theorem AlgRes.volume_preimage_eq_zero {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (A : FinHolAtlas e R.M) (hA : R.IsGoodAtlas A) (j : Fin A.n) :
    MeasureTheory.volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
      {x | ∃ i, x ∈ R.src i ∧ (fun q => eval (R.coord i x) (R.lift i q)) ∈ conePts D}) = 0 := by
  classical
  have hset : (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      {x | ∃ i, x ∈ R.src i ∧ (fun q => eval (R.coord i x) (R.lift i q)) ∈ conePts D} =
      ⋃ i, ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
        {x | x ∈ R.src i ∧ (fun q => eval (R.coord i x) (R.lift i q)) ∈ conePts D}) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h1, i, h2⟩; exact ⟨i, h1, h2⟩
    · rintro ⟨i, h1, h2⟩; exact ⟨h1, i, h2⟩
  have hyp : ∀ l : Fin e, MeasureTheory.volume {w : Fin e → ℂ | w l = 0} = 0 := by
    intro l
    have : {w : Fin e → ℂ | w l = 0} =
        Set.univ.pi (Function.update (fun _ => (Set.univ : Set ℂ)) l {0}) := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
      constructor
      · intro hw k
        by_cases hk : k = l
        · subst hk; simp [hw]
        · simp [Function.update_of_ne hk]
      · intro hw; simpa using hw l
    rw [this, MeasureTheory.volume_pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp)
  rw [hset]
  refine MeasureTheory.measure_iUnion_null fun i => ?_
  apply MeasureTheory.measure_null_of_locally_null
  rintro y0 ⟨hy0t, hy0s, -⟩
  obtain ⟨ψ, hψc, hxψ, hψs, hψe⟩ := hA.2 i _ hy0s (R.sncAt i _ hy0s).r (R.sncAt i _ hy0s).span_eq
    _ (R.isOpen_nonvan i (R.sncAt i _ hy0s).h) ⟨hy0s, (R.sncAt i _ hy0s).eval_h⟩
  set d := R.sncAt i _ hy0s with hd
  have hU : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target ψ.open_source
  refine ⟨_, inter_mem_nhdsWithin _ (hU.mem_nhds ⟨hy0t, hxψ⟩), ?_⟩
  have hN : MeasureTheory.volume ((ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) ∩
      {w : Fin e → ℂ | ∏ l ∈ d.J, w l = 0}) = 0 := by
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_iUnion_null hyp)
    rintro w ⟨-, hw⟩
    obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.1 hw
    exact Set.mem_iUnion.2 ⟨l, hl⟩
  have hg : DifferentiableOn ℝ ((A.chart j) ∘ ψ.symm)
      ((ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) ∩ {w : Fin e → ℂ | ∏ l ∈ d.J, w l = 0}) :=
    fun w hw => (((hψc j).2 w hw.1).differentiableAt.restrictScalars ℝ).differentiableWithinAt
  refine MeasureTheory.measure_mono_null ?_
    (MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _ hg hN)
  rintro y ⟨⟨hyt, hys, hyD⟩, -, hyψ⟩
  refine ⟨ψ ((A.chart j).symm y), ⟨⟨ψ.map_source hyψ, ?_⟩, ?_⟩, ?_⟩
  · rw [Set.mem_preimage, ψ.left_inv hyψ]; exact (A.chart j).map_target hyt
  · have hbd := (R.zero_bd i _ hys).2 hyD _ d.mem_bd
    rw [map_mul, map_prod] at hbd
    have h0 := (mul_eq_zero.1 hbd).resolve_left (hψs hyψ).1.2
    simp only [Set.mem_ofPred_eq, hψe _ hyψ]
    exact h0
  · simp only [Function.comp_apply, ψ.left_inv hyψ, (A.chart j).right_inv hyt]

end ReciprocityTheory.AnForm.R
