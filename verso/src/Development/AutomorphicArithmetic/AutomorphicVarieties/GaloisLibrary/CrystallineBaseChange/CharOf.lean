import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.IntOfIntegers
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.MemMirabIff
import Mathlib.GroupTheory.FiniteAbelian.Duality

open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Nf Matrix

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (Matrix.scalar (Fin 2) u.val i j) = Matrix.scalar (Fin 2) (1 - s 1 + s u.val) i j`. Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.one_apply, e]`.
-/
private theorem corner_sc {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (u : Rˣ) :
    cornerGL 2 s (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (Units.map (corner s) u) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (Matrix.scalar (Fin 2) u.val i j) =
    Matrix.scalar (Fin 2) (1 - s 1 + s u.val) i j
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

/- English proof (translation)
Establish `h1 : ∀ g, HasDerivAt (fun t : ℝ => φ.1 (g * infGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) 0 0`. Introduce `g`. Establish `h1` using `hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z))) (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by`. Use `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_` and prove the remaining obligations. Distinguish the cases in `e : i = j`.

Substitute `e` using the available equality. Use `((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp` as an intermediate fact. Simplify using `using this`. Simplify `hasDerivAt_const (0 : ℝ) (0 : ℝ))` using `[Matrix.diagonal_apply, e]`. Establish `e : lieD (toL (Matrix.scalar (Fin 2) z)) φ.1 g = 0` using `congrArg (fun ψ : Sm ℚ 2 => ψ.1 g) h`.

Conclude with `e ▸ h1`. Establish `h2 : ∀ s, HasDerivAt (fun t : ℝ => φ.1 (g * infGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) 0 s`. Introduce `s`. Establish `h3` using `h1 (g * infGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (expU (s • z))))`. Rewrite `h3` using `[← sub_self s]`.

Establish `h4` using `h3.comp_sub_const s s`. Use `h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[mul_assoc, ← map_mul, ← map_mul, ← TR.expU_add, ← add_smul, add_sub_cancel]`. Use `is_const_of_deriv_eq_zero (fun s => (h2 s).differentiableAt) (fun s => (h2 s).deriv) t 0` as an intermediate fact.

Simplify `this` using `[TR.expU_zero]`.
-/
private theorem flow_const (φ : Sm ℚ 2) (z : Rinf ℚ) (h : lie ℚ 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0) (g : GA ℚ 2) (t : ℝ) :
    φ.1 (g * infGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))) = φ.1 g := by
  have h1 : ∀ g, HasDerivAt (fun t : ℝ => φ.1 (g * infGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) 0 0 := by
    intro g
    have h1 := hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
      (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
        refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
        by_cases e : i = j
        · subst e
          have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
          simpa using this
        · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have e : lieD (toL (Matrix.scalar (Fin 2) z)) φ.1 g = 0 := congrArg (fun ψ : Sm ℚ 2 => ψ.1 g) h
    exact e ▸ h1
  have h2 : ∀ s, HasDerivAt (fun t : ℝ => φ.1 (g * infGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) 0 s := by
    intro s
    have h3 := h1 (g * infGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (expU (s • z))))
    rw [← sub_self s] at h3
    have h4 := h3.comp_sub_const s s
    refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [mul_assoc, ← map_mul, ← map_mul, ← TR.expU_add, ← add_smul, add_sub_cancel]
  have := is_const_of_deriv_eq_zero (fun s => (h2 s).differentiableAt) (fun s => (h2 s).deriv) t 0
  simpa [TR.expU_zero] using this

/- English proof (translation)
Take `⟨y, hy, hd⟩` from `hd`. Take `⟨z, hz, he⟩` from `he`. Establish `hM' : (M : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `h0 : algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * M = 1`. Rewrite using `[← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hM', map_one]`.

Establish `h1 : algebraMap ℚ (Af ℚ) ((M : ℚ)⁻¹ * ((e : ℚ) - d)) = y - z`. Rewrite using `[map_mul, map_sub, map_intCast, map_intCast]`. Take the linear combination `algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * (hd - he) + (y - z) * h0`. Take `⟨n, hn⟩` from `ratAd.2.2 _ (h1 ▸ sub_mem hy hz)`. Rewrite using `[ZMod.intCast_eq_intCast_iff_dvd_sub]`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite `hn` using `[inv_mul_eq_iff_eq_mul₀ hM']`. Conclude with `hn` after adjusting the coercions.
-/
private theorem red_uniq {M : ℕ} (hM : 1 ≤ M) {x : Af ℚ} {d e : ℤ} (hd : ∃ y ∈ Af.Ohat ℚ, x - d = M * y)
    (he : ∃ y ∈ Af.Ohat ℚ, x - e = M * y) : (d : ZMod M) = e := by
  obtain ⟨y, hy, hd⟩ := hd
  obtain ⟨z, hz, he⟩ := he
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h0 : algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * M = 1 := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hM', map_one]
  have h1 : algebraMap ℚ (Af ℚ) ((M : ℚ)⁻¹ * ((e : ℚ) - d)) = y - z := by
    rw [map_mul, map_sub, map_intCast, map_intCast]
    linear_combination algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * (hd - he) + (y - z) * h0
  obtain ⟨n, hn⟩ := ratAd.2.2 _ (h1 ▸ sub_mem hy hz)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨n, ?_⟩
  rw [inv_mul_eq_iff_eq_mul₀ hM'] at hn
  exact_mod_cast hn

/- English proof (translation)
Use `choose f hf using fun x : ↥(Af.Ohat ℚ) => ratAd.2.1 M hM x x.2`. Use `⟨⟨⟨fun x => f x, ?_⟩, fun a b => ?_⟩, fun x d h => red_uniq hM (hf x) h, fun x hx => ?_⟩` and prove the remaining obligations. Use `red_uniq hM (e := 1) (hf 1) ⟨0, zero_mem _, by simp⟩` as an intermediate fact. Simplify using `using this`. Take `⟨y, hy, h1⟩` from `hf a`.

Take `⟨z, hz, h2⟩` from `hf b`. Use `red_uniq hM (e := f a * f b) (hf (a * b)) ⟨a * z + f b * y, add_mem (mul_mem a.2 hz) (mul_mem (intCast_mem _ _) hy), by` as an intermediate fact. Rewrite using `[Subring.coe_mul, Int.cast_mul]`. Take the linear combination `(a : Af ℚ) * h2 + (f b : Af ℚ) * h1⟩`. Simplify using `using this`.

Take `⟨y, hy, h1⟩` from `hf x`. Establish `h2 : ((1 : ℤ) : ZMod M) = f x` using `by rw [Int.cast_one]; exact hx.symm`. Take `⟨n, hn⟩` from `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h2`. Establish `h3` using `congrArg (Int.cast : ℤ → Af ℚ) hn`. Move the coercions through the operations in `at h3`.

Conclude with `⟨y + n, add_mem hy (intCast_mem _ _), by linear_combination h1 + h3⟩`.
-/
private theorem red_ex {M : ℕ} (hM : 1 ≤ M) : ∃ ρ : ↥(Af.Ohat ℚ) →* ZMod M,
    (∀ (x : ↥(Af.Ohat ℚ)) (d : ℤ), (∃ y ∈ Af.Ohat ℚ, (x : Af ℚ) - d = M * y) → ρ x = d) ∧
    ∀ x, ρ x = 1 → ∃ y ∈ Af.Ohat ℚ, (x : Af ℚ) - 1 = M * y := by
  choose f hf using fun x : ↥(Af.Ohat ℚ) => ratAd.2.1 M hM x x.2
  refine ⟨⟨⟨fun x => f x, ?_⟩, fun a b => ?_⟩, fun x d h => red_uniq hM (hf x) h, fun x hx => ?_⟩
  · have := red_uniq hM (e := 1) (hf 1) ⟨0, zero_mem _, by simp⟩
    simpa using this
  · obtain ⟨y, hy, h1⟩ := hf a
    obtain ⟨z, hz, h2⟩ := hf b
    have := red_uniq hM (e := f a * f b) (hf (a * b)) ⟨a * z + f b * y,
      add_mem (mul_mem a.2 hz) (mul_mem (intCast_mem _ _) hy), by
        rw [Subring.coe_mul, Int.cast_mul]
        linear_combination (a : Af ℚ) * h2 + (f b : Af ℚ) * h1⟩
    simpa using this
  · obtain ⟨y, hy, h1⟩ := hf x
    have h2 : ((1 : ℤ) : ZMod M) = f x := by rw [Int.cast_one]; exact hx.symm
    obtain ⟨n, hn⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h2
    have h3 := congrArg (Int.cast : ℤ → Af ℚ) hn
    push_cast at h3
    exact ⟨y + n, add_mem hy (intCast_mem _ _), by linear_combination h1 + h3⟩

/- English proof (translation)
Establish `hs` using `π.rangeRestrict_surjective`. Set `f : π.range →* ℂˣ` to `MonoidHom.liftOfSurjective _ hs ⟨ψ, by rwa [MonoidHom.ker_rangeRestrict]⟩`. Establish `hf : ∀ g, f (π.rangeRestrict g) = ψ g` using `fun g => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g`. Take `⟨F, hF⟩` from `MonoidHom.domRestrict_surjective ℂ π.range f`. Use `⟨MulChar.ofUnitHom F, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hf, ← hF]`. Simplify using the standard rewrite rules.
-/
private theorem ext_char {G : Type} [CommGroup G] {N : ℕ} [NeZero N] (π : G →* (ZMod N)ˣ) (ψ : G →* ℂˣ) (h : π.ker ≤ ψ.ker) :
    ∃ χ : DirichletCharacter ℂ N, ∀ g, χ (π g) = ψ g := by
  have hs := π.rangeRestrict_surjective
  let f : π.range →* ℂˣ := MonoidHom.liftOfSurjective _ hs ⟨ψ, by rwa [MonoidHom.ker_rangeRestrict]⟩
  have hf : ∀ g, f (π.rangeRestrict g) = ψ g := fun g => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  obtain ⟨F, hF⟩ := MonoidHom.domRestrict_surjective ℂ π.range f
  refine ⟨MulChar.ofUnitHom F, fun g => ?_⟩
  rw [← hf, ← hF]
  simp

/- English proof (translation)
Introduce `N hN ω φ hφ hE hK hc`. Establish `: NeZero N` using `⟨by omega⟩`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hφ (Subtype.ext (funext h))`. Establish `key : ∀ z : Ideles ℚ, φ.1 (g * GeneralLinearGroup.scalar (Fin 2) z) = φ.1 g → ω.1 z = 1` using `fun z h => by`. Rewrite `h` using `[← GeneralLinearGroup.scalar_commute, hc]`. Conclude with `Units.ext (mul_right_cancel₀ hg (h.trans (one_mul _).symm))`. Take `⟨ρ, hρ, hρ1⟩` from `red_ex hN`.

Set `j : (↥(Af.Ohat ℚ))ˣ →* (Af ℚ)ˣ` to `Units.map (Af.Ohat ℚ).subtype.toMonoidHom`. Take `⟨χ, hχ⟩` from `ext_char (Units.map ρ) (ω.1.comp ((finId ℚ).comp j))⁻¹ (fun u hu => by`. Establish `h1 : ρ u = 1` using `congrArg Units.val hu`. Establish `h2 : GeneralLinearGroup.scalar (Fin 2) (j u) ∈ K1G N`. Establish `hm : ∀ w a b, GeneralLinearGroup.scalar (Fin 2) (j w) a b ∈ Af.Ohat ℚ` using `fun w a b => by`.

Distinguish the cases in `e : a = b`. Simplify using `[e, j]`. Simplify using `[e]`. Use `(memK N _).2 ⟨hm u, ?_, ⟨0, zero_mem _, by simp⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv, ← map_inv]`.

Conclude with `hm _`. Simplify `hρ1 u h1` using `[j]`. Establish `h3 : φ.1 (g * finGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (j u))) = φ.1 g` using `congrFun (congrArg Subtype.val (hK _ h2)) g`. Establish `s3 : finGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (j u)) = GeneralLinearGroup.scalar (Fin 2) (finId ℚ (j u))` using `corner_sc _ _`. Rewrite `h3` using `[s3]`.

Express the relevant statement in the definitionally equal form `(ω.1 (finId ℚ (j u)))⁻¹ = 1`. Rewrite using `[key _ h3, inv_one])`. Use `⟨χ, fun t ht => ?_, fun u hu d hd => ?_⟩` and prove the remaining obligations. Establish `h0 : lie ℚ 2 (toL (Matrix.scalar (Fin 2) (Pi.single Rat.infinitePlace 1))) φ = 0`. Rewrite using `[← hE Rat.infinitePlace, TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add]`.

Use `congr 2`. Use extensionality with `i j v`. Rewrite using `[Subsingleton.elim v Rat.infinitePlace]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`. Establish `h1` using `flow_const φ _ h0 g (Real.log (t.val Rat.infinitePlace))`.

Establish `h2 : expU (Real.log (t.val Rat.infinitePlace) • (Pi.single Rat.infinitePlace 1 : Rinf ℚ)) = t`. Use `Units.ext (funext fun v => ?_)` and prove the remaining obligations. Rewrite using `[Subsingleton.elim v Rat.infinitePlace]`. Simplify using `[Real.exp_log (ht _)]`. Establish `s2 : infGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) t) = GeneralLinearGroup.scalar (Fin 2) (infId ℚ t)` using `corner_sc _ _`.

Rewrite `h1` using `[h2, s2]`. Conclude with `key _ h1`. Set `u' : (↥(Af.Ohat ℚ))ˣ` to `⟨⟨u, hu.1⟩, ⟨_, hu.2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩`. Establish `h1 : χ (ρ ⟨u, hu.1⟩) = ((ω.1 (finId ℚ u))⁻¹ : ℂˣ)` using `hχ u'`. Rewrite using `[← hρ ⟨u, hu.1⟩ d hd, h1]`.

Conclude with `Units.mul_inv _`.
-/
theorem UpperTheory.V.Br.charOf :
    UpperTheory.V.Br.CharOf := by
  intro N hN ω φ hφ hE hK hc
  have : NeZero N := ⟨by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (Subtype.ext (funext h))
  have key : ∀ z : Ideles ℚ, φ.1 (g * GeneralLinearGroup.scalar (Fin 2) z) = φ.1 g → ω.1 z = 1 := fun z h => by
    rw [← GeneralLinearGroup.scalar_commute, hc] at h
    exact Units.ext (mul_right_cancel₀ hg (h.trans (one_mul _).symm))
  obtain ⟨ρ, hρ, hρ1⟩ := red_ex hN
  let j : (↥(Af.Ohat ℚ))ˣ →* (Af ℚ)ˣ := Units.map (Af.Ohat ℚ).subtype.toMonoidHom
  obtain ⟨χ, hχ⟩ := ext_char (Units.map ρ) (ω.1.comp ((finId ℚ).comp j))⁻¹ (fun u hu => by
    have h1 : ρ u = 1 := congrArg Units.val hu
    have h2 : GeneralLinearGroup.scalar (Fin 2) (j u) ∈ K1G N := by
      have hm : ∀ w a b, GeneralLinearGroup.scalar (Fin 2) (j w) a b ∈ Af.Ohat ℚ := fun w a b => by
        by_cases e : a = b
        · simp [e, j]
        · simp [e]
      refine (memK N _).2 ⟨hm u, ?_, ⟨0, zero_mem _, by simp⟩, ?_⟩
      · rw [← map_inv, ← map_inv]
        exact hm _
      · simpa [j] using hρ1 u h1
    have h3 : φ.1 (g * finGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (j u))) = φ.1 g :=
      congrFun (congrArg Subtype.val (hK _ h2)) g
    have s3 : finGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (j u)) = GeneralLinearGroup.scalar (Fin 2) (finId ℚ (j u)) :=
      corner_sc _ _
    rw [s3] at h3
    change (ω.1 (finId ℚ (j u)))⁻¹ = 1
    rw [key _ h3, inv_one])
  refine ⟨χ, fun t ht => ?_, fun u hu d hd => ?_⟩
  · classical
    have h0 : lie ℚ 2 (toL (Matrix.scalar (Fin 2) (Pi.single Rat.infinitePlace 1))) φ = 0 := by
      rw [← hE Rat.infinitePlace, TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add]
      congr 2
      ext i j v
      rw [Subsingleton.elim v Rat.infinitePlace]
      fin_cases i <;> fin_cases j <;> simp
    have h1 := flow_const φ _ h0 g (Real.log (t.val Rat.infinitePlace))
    have h2 : expU (Real.log (t.val Rat.infinitePlace) • (Pi.single Rat.infinitePlace 1 : Rinf ℚ)) = t := by
      refine Units.ext (funext fun v => ?_)
      rw [Subsingleton.elim v Rat.infinitePlace]
      simp [Real.exp_log (ht _)]
    have s2 : infGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) t) = GeneralLinearGroup.scalar (Fin 2) (infId ℚ t) :=
      corner_sc _ _
    rw [h2, s2] at h1
    exact key _ h1
  · let u' : (↥(Af.Ohat ℚ))ˣ := ⟨⟨u, hu.1⟩, ⟨_, hu.2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
    have h1 : χ (ρ ⟨u, hu.1⟩) = ((ω.1 (finId ℚ u))⁻¹ : ℂˣ) := hχ u'
    rw [← hρ ⟨u, hu.1⟩ d hd, h1]
    exact Units.mul_inv _
