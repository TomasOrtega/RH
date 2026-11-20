import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.ExistsPadicIntLiftOfIntegralAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.YLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.YNear

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

/- English proof (translation)
Establish `haN : a.Coprime l` using `Nat.Coprime.coprime_dvd_right hl ha`. Establish `haM : a.Coprime M`. Rewrite using `[hM]`. Conclude with `Nat.Coprime.mul_right ha (Nat.Coprime.pow_right m haN)`. Establish `hdiv : l ^ (r + ck l (e + 1) + 1) ∣ M`.

Rewrite using `[hM]`. Conclude with `Dvd.dvd.mul_left (pow_dvd_pow l hm) N`. Establish `hI` using `yNear l Γ M (φ.comp (ZMod.unitsMap h)) e a r haM ho hdiv`. Rewrite `hI` using `[yLevel l Γ N φ (e + 1) a ha (by omega) hl m M h haM hM]`. Use `(intAt_iff l r _).mp hI g` as an intermediate fact.

Simplify `this` using `[coeff_coefMap]`.
-/
private theorem near_level (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N]
    (φ : (ZMod N)ˣ →* Γ) (e a : ℕ) (ha : a.Coprime N) (ho : Odd a) (hl : l ∣ N) (r m : ℕ)
    (hm : r + ck l (e + 1) + 1 ≤ m) (M : ℕ) [NeZero M] (h : N ∣ M) (hM : M = N * l ^ m) (g : Γ) :
    InPow l r ((yEl (e + 1) a ha φ).coeff g - (((ytEl e a (φ.comp (ZMod.unitsMap h))).coeff g : ℤ) : ℚ)) := by
  have haN : a.Coprime l := Nat.Coprime.coprime_dvd_right hl ha
  have haM : a.Coprime M := by
    rw [hM]
    exact Nat.Coprime.mul_right ha (Nat.Coprime.pow_right m haN)
  have hdiv : l ^ (r + ck l (e + 1) + 1) ∣ M := by
    rw [hM]
    exact Dvd.dvd.mul_left (pow_dvd_pow l hm) N
  have hI := yNear l Γ M (φ.comp (ZMod.unitsMap h)) e a r haM ho hdiv
  rw [yLevel l Γ N φ (e + 1) a ha (by omega) hl m M h haM hM] at hI
  have := (intAt_iff l r _).mp hI g
  simpa [coeff_coefMap] using this

/- English proof (translation)
Introduce `l _ Γ _ _ N _ φ e a ha ho hl`. Establish `hl0 : l ≠ 0` using `(Fact.out : l.Prime).ne_zero`. Use `set y := yEl (e + 1) a ha φ with hy`. Establish `hy0 : IntAt l 0 y`. Rewrite using `[intAt_iff]`.

Introduce `g`. Use `haveI : NeZero (N * l ^ (ck l (e + 1) + 1)) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl0)⟩`. Establish `hn` using `near_level l Γ N φ e a ha ho hl 0 (ck l (e + 1) + 1) (by omega) (N * l ^ (ck l (e + 1) + 1)) (dvd_mul_right _ _) rfl g`. Establish `h1` using `hn.mem`. Establish `h2` using `add_mem h1 (intCast_mem (Zl l) ((ytEl e a (φ.comp (ZMod.unitsMap (dvd_mul_right N (l ^ (ck l (e + 1) + 1)))))).coeff g))`.

Rewrite `h2` using `[sub_add_cancel]`. Use `show y.coeff g / (l : ℚ) ^ 0 ∈ Zl l`. Simplify using `using h2`. Take `⟨Yp, hYp⟩` from `exists_padicInt_lift_of_integralAt l y hy0`. Establish `hYg : ∀ g, ((Yp.coeff g : ℤ_[l]) : ℚ_[l]) = ((y.coeff g : ℚ) : ℚ_[l])`.

Introduce `g`. Use `congrArg (fun x => x.coeff g) hYp` as an intermediate fact. Simplify using `using this`. Use `⟨Yp, hYg, ?_⟩` and prove the remaining obligations. Introduce `r`.

Use `⟨r + ck l (e + 1) + 1, ?_⟩` and prove the remaining obligations. Introduce `m hm M _ h hM`. Establish `hc : ∀ g, ∃ c : ℤ_[l], (((ytEl e a (φ.comp (ZMod.unitsMap h))).coeff g : ℤ) : ℤ_[l]) = Yp.coeff g + (l : ℤ_[l]) ^ r * c`. Introduce `g`. Establish `hn` using `near_level l Γ N φ e a ha ho hl r m hm M h hM g`.

Use `set t : ℤ := (ytEl e a (φ.comp (ZMod.unitsMap h))).coeff g`. Use `set q : ℚ := (y.coeff g - (t : ℚ)) / (l : ℚ) ^ r with hqdef`. Establish `hq : ‖(q : ℚ_[l])‖ ≤ 1` using `Padic.norm_rat_le_one (mem_Zl.mp hn)`. Establish `hqr : q * (l : ℚ) ^ r = y.coeff g - t`. Rewrite using `[hqdef]`.

Conclude with `div_mul_cancel₀ _ (pow_ne_zero _ (by exact_mod_cast hl0))`. Establish `hqr' : (q : ℚ_[l]) * (l : ℚ_[l]) ^ r = ((y.coeff g : ℚ) : ℚ_[l]) - (t : ℚ_[l])`. Use `congrArg (fun x : ℚ => (x : ℚ_[l])) hqr` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.

Set `c : ℤ_[l]` to `⟨(q : ℚ_[l]), hq⟩`. Use `⟨-c, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (t : ℚ_[l]) = ((Yp.coeff g : ℤ_[l]) : ℚ_[l]) + (l : ℚ_[l]) ^ r * -(q : ℚ_[l])`. Rewrite using `[hYg g]`.

Take the linear combination `hqr'`. Use `choose c hc using hc`. Use `⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c), ?_⟩` and prove the remaining obligations. Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Use extensionality with `g`.

Rewrite using `[MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_smul, coeff_coefMap, hc g]`. Simplify using `[smul_eq_mul]`.
-/
theorem UpperTheory.V.Odd.congr :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (e a : ℕ) (ha : a.Coprime N), Odd a → l ∣ N → ∃ z : MonoidAlgebra ℤ_[l] Γ, IsInt l z (yEl (e + 1) a ha φ) ∧ ∀ r : ℕ, ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (M : ℕ) [NeZero M] (h : N ∣ M), M = N * l ^ m → ∃ w : MonoidAlgebra ℤ_[l] Γ, coefMap ℤ_[l] Γ (ytEl e a (φ.comp (ZMod.unitsMap h))) = z + (l : ℤ_[l]) ^ r • w := by
  intro l _ Γ _ _ N _ φ e a ha ho hl
  classical
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  set y := yEl (e + 1) a ha φ with hy
  have hy0 : IntAt l 0 y := by
    rw [intAt_iff]
    intro g
    haveI : NeZero (N * l ^ (ck l (e + 1) + 1)) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl0)⟩
    have hn := near_level l Γ N φ e a ha ho hl 0 (ck l (e + 1) + 1) (by omega)
      (N * l ^ (ck l (e + 1) + 1)) (dvd_mul_right _ _) rfl g
    have h1 := hn.mem
    have h2 := add_mem h1 (intCast_mem (Zl l) ((ytEl e a (φ.comp (ZMod.unitsMap
      (dvd_mul_right N (l ^ (ck l (e + 1) + 1)))))).coeff g))
    rw [sub_add_cancel] at h2
    show y.coeff g / (l : ℚ) ^ 0 ∈ Zl l
    simpa using h2
  obtain ⟨Yp, hYp⟩ := exists_padicInt_lift_of_integralAt l y hy0
  have hYg : ∀ g, ((Yp.coeff g : ℤ_[l]) : ℚ_[l]) = ((y.coeff g : ℚ) : ℚ_[l]) := by
    intro g
    have := congrArg (fun x => x.coeff g) hYp
    simpa using this
  refine ⟨Yp, hYg, ?_⟩
  intro r
  refine ⟨r + ck l (e + 1) + 1, ?_⟩
  intro m hm M _ h hM
  have hc : ∀ g, ∃ c : ℤ_[l], (((ytEl e a (φ.comp (ZMod.unitsMap h))).coeff g : ℤ) : ℤ_[l]) =
      Yp.coeff g + (l : ℤ_[l]) ^ r * c := by
    intro g
    have hn := near_level l Γ N φ e a ha ho hl r m hm M h hM g
    set t : ℤ := (ytEl e a (φ.comp (ZMod.unitsMap h))).coeff g
    set q : ℚ := (y.coeff g - (t : ℚ)) / (l : ℚ) ^ r with hqdef
    have hq : ‖(q : ℚ_[l])‖ ≤ 1 := Padic.norm_rat_le_one (mem_Zl.mp hn)
    have hqr : q * (l : ℚ) ^ r = y.coeff g - t := by
      rw [hqdef]
      exact div_mul_cancel₀ _ (pow_ne_zero _ (by exact_mod_cast hl0))
    have hqr' : (q : ℚ_[l]) * (l : ℚ_[l]) ^ r = ((y.coeff g : ℚ) : ℚ_[l]) - (t : ℚ_[l]) := by
      have := congrArg (fun x : ℚ => (x : ℚ_[l])) hqr
      push_cast at this
      exact this
    let c : ℤ_[l] := ⟨(q : ℚ_[l]), hq⟩
    refine ⟨-c, ?_⟩
    apply Subtype.ext
    show (t : ℚ_[l]) = ((Yp.coeff g : ℤ_[l]) : ℚ_[l]) + (l : ℚ_[l]) ^ r * -(q : ℚ_[l])
    rw [hYg g]
    linear_combination hqr'
  choose c hc using hc
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c), ?_⟩
  apply MonoidAlgebra.ext
  ext g
  rw [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_smul, coeff_coefMap, hc g]
  simp [smul_eq_mul]
