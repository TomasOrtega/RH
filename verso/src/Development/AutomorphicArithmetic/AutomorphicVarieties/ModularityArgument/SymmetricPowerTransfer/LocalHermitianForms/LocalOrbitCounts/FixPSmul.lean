import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.WTrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Descent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.SplitS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.Fst
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.MemCOfInt

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

section
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {Δ τ : K}

variable (Δ) in
private def cmb (s : K) (a b : Etau K τ) : EL Δ τ := ⟨⟨a.re, s * b.re⟩, ⟨a.im, s * b.im⟩⟩

variable (O Δ) in
private def Phi (g s : K) (S : Set (Etau K τ)) : Set (Sp Δ τ) :=
  {x | IsInt O (g • x.1) ∧ ∃ a ∈ S, ∃ b ∈ S, x.2 = cmb Δ s a b}

/- English proof (translation)
Use `⟨⟨x.re.re, x.im.re⟩, ⟨x.re.im / s, x.im.im / s⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [cmb, mul_div_cancel₀ _ hs]`.
-/
private theorem cmb_ex {s : K} (hs : s ≠ 0) (x : EL Δ τ) : ∃ a b, x = cmb Δ s a b := by
  refine ⟨⟨x.re.re, x.im.re⟩, ⟨x.re.im / s, x.im.im / s⟩, ?_⟩
  ext <;> simp [cmb, mul_div_cancel₀ _ hs]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [cmb, ofE]`.
-/
private theorem cmb_zero (s : K) (a : Etau K τ) : cmb Δ s a 0 = ofE Δ a := by
  ext <;> simp [cmb, ofE]

/- English proof (translation)
Establish `h1` using `congrArg (fun x : EL Δ τ => x.re.re) h`. Establish `h2` using `congrArg (fun x : EL Δ τ => x.im.re) h`. Conclude with `QuadraticAlgebra.ext h1 h2`.
-/
private theorem cmb_inj {s : K} {a a' b b' : Etau K τ} (h : cmb Δ s a b = cmb Δ s a' b') : a = a' := by
  have h1 := congrArg (fun x : EL Δ τ => x.re.re) h
  have h2 := congrArg (fun x : EL Δ τ => x.im.re) h
  exact QuadraticAlgebra.ext h1 h2

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [cmb, ofE] <;> ring`.
-/
private theorem ofE_cmb (s : K) (v a b : Etau K τ) : ofE Δ v * cmb Δ s a b = cmb Δ s (v * a) (v * b) := by
  ext <;> simp [cmb, ofE] <;> ring

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [herm, cmb, ofE, sigL, QuadraticAlgebra.trace, Algebra.smul_def] <;> ring`.
-/
private theorem herm_cmb (c s t : K) (x y : Lsq K Δ) (a b a' b' : Etau K τ) :
    herm c ((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) (x, cmb Δ s a b) (y, cmb Δ s a' b') =
      c • (x * star y) + ⟨Δ * s ^ 2 * (t * (τ ^ 2 - 4) * (b * star a').im - t * (τ ^ 2 - 4) * (a * star b').im),
        s * (t * (τ ^ 2 - 4) * (a * star a').im - Δ * s ^ 2 * (t * (τ ^ 2 - 4) * (b * star b').im))⟩ := by
  ext <;> simp [herm, cmb, ofE, sigL, QuadraticAlgebra.trace, Algebra.smul_def] <;> ring

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [cmb, ofE, semi, sigL] <;> ring`.
-/
private theorem semi_cmb (s p q : K) (v a b : Etau K τ) (x : Lsq K Δ) :
    semi ((⟨p, s * q⟩ : Lsq K Δ) • ofE Δ v) (x, cmb Δ s a b) =
      (star x, cmb Δ s (p • (v * a) - (Δ * s ^ 2 * q) • (v * b)) (q • (v * a) - p • (v * b))) := by
  ext <;> simp [cmb, ofE, semi, sigL] <;> ring

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨hy1, a, ha, b, hb, hy2⟩, rfl⟩`. Use `⟨hy1, quo z * a, ⟨a, ha, rfl⟩, quo z * b, ⟨b, hb, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [tor, hy2, ofE_cmb]`.

Introduce and unpack `⟨hx1, _, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hx2⟩`. Use `⟨(x.1, cmb Δ s a b), ⟨hx1, a, ha, b, hb, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [tor, ofE_cmb, ← hx2]`.
-/
private theorem phi_act (g s : K) (S : Set (Etau K τ)) (z : (Etau K τ)ˣ) :
    tor Δ z '' Phi O Δ g s S = Phi O Δ g s ((quo z * ·) '' S) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy1, a, ha, b, hb, hy2⟩, rfl⟩
    refine ⟨hy1, quo z * a, ⟨a, ha, rfl⟩, quo z * b, ⟨b, hb, rfl⟩, ?_⟩
    simp only [tor, hy2, ofE_cmb]
  · rintro ⟨hx1, _, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hx2⟩
    refine ⟨(x.1, cmb Δ s a b), ⟨hx1, a, ha, b, hb, rfl⟩, ?_⟩
    simp only [tor, ofE_cmb, ← hx2]

/- English proof (translation)
Take `⟨x1, x2⟩` from `x`. Establish `hν2 : ν.re ^ 2 - Δ * ν.im ^ 2 = -1`. Simplify using `[QuadraticAlgebra.norm] at hν`. Take the linear combination `hν`. Establish `hu2 : u.re ^ 2 + τ * u.re * u.im + u.im ^ 2 = 1`.

Simplify using `[QuadraticAlgebra.norm] at hu`. Take the linear combination `hu`. Apply the tactic sequence `ext <;> simp [semi, ofE, sigL, Algebra.smul_def] <;> ring_nf`. Apply the tactic sequence `all_goals first`. Consider the case `linear_combination (-(u.re ^ 2 + τ * u.re * u.im + u.im ^ 2) * x2.re.re) * hν2 + x2.re.re * hu2`.

Consider the case `linear_combination (-(u.re ^ 2 + τ * u.re * u.im + u.im ^ 2) * x2.re.im) * hν2 + x2.re.im * hu2`. Consider the case `linear_combination (-(u.re ^ 2 + τ * u.re * u.im + u.im ^ 2) * x2.im.re) * hν2 + x2.im.re * hu2`. Consider the case `linear_combination (-(u.re ^ 2 + τ * u.re * u.im + u.im ^ 2) * x2.im.im) * hν2 + x2.im.im * hu2`.
-/
private theorem semi_inv {u : Etau K τ} (hu : QuadraticAlgebra.norm u = 1) {ν : Lsq K Δ} (hν : QuadraticAlgebra.norm ν = -1)
    (x : Sp Δ τ) : semi (ν • ofE Δ u) (semi ((-ν) • ofE Δ (star u)) x) = x := by
  obtain ⟨x1, x2⟩ := x
  have hν2 : ν.re ^ 2 - Δ * ν.im ^ 2 = -1 := by
    simp [QuadraticAlgebra.norm] at hν
    linear_combination hν
  have hu2 : u.re ^ 2 + τ * u.re * u.im + u.im ^ 2 = 1 := by
    simp [QuadraticAlgebra.norm] at hu
    linear_combination hu
  ext <;> simp [semi, ofE, sigL, Algebra.smul_def] <;> ring_nf
  all_goals first
    | linear_combination (-(u.re ^ 2 + τ * u.re * u.im + u.im ^ 2) * x2.re.re) * hν2 + x2.re.re * hu2
    | linear_combination (-(u.re ^ 2 + τ * u.re * u.im + u.im ^ 2) * x2.re.im) * hν2 + x2.re.im * hu2
    | linear_combination (-(u.re ^ 2 + τ * u.re * u.im + u.im ^ 2) * x2.im.re) * hν2 + x2.im.re * hu2
    | linear_combination (-(u.re ^ 2 + τ * u.re * u.im + u.im ^ 2) * x2.im.im) * hν2 + x2.im.im * hu2

/- English proof (translation)
Establish `e1` using `congrArg QuadraticAlgebra.re hu2`. Establish `e2` using `congrArg QuadraticAlgebra.im hu2`. Simplify using `[pow_two] at e1 e2`. Simplify using `[QuadraticAlgebra.norm] at hu hν`. Establish `hΔ : Δ ≠ 0` using `left_ne_zero_of_mul hs`.

Establish `hs0 : s ≠ 0` using `fun h => hs (by simp [h])`. Establish `hdd : (ν • ofE Δ u) * star (sigL (ν • ofE Δ u)) = -1`. Apply the tactic sequence `ext <;> simp [sigL, ofE]`. Take the linear combination `(u.re * u.re + τ * u.re * u.im + u.im * u.im) * hν - hu`. Apply the tactic sequence `all_goals ring`.

Establish `hsm : sigL ((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) = -((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ))`. Apply the tactic sequence `ext <;> simp [sigL, ofE] <;> ring`. Establish `hmm : ((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) * ((algebraMap K (Lsq K Δ) (t ^ 2 * (Δ * s ^ 2) * (τ ^ 2 - 4))⁻¹) • ((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ))) = 1`. Apply the tactic sequence `ext <;> simp [ofE]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `all_goals ring`. Use `⟨hτ, hc, ?_, ⟨⟨_, _, hmm, by rw [mul_comm]; exact hmm⟩, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [sigL, ofE]`. Take the linear combination `(ν.re * ν.re - Δ * ν.im * ν.im) * e1`.

Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(u.re * u.im + u.im * u.re + τ * u.im * u.im) * hν - e2`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `ext <;> simp [sigL, ofE] <;> ring`. Rewrite using `[hsm, mul_assoc, hdd]`.

Simplify using the standard rewrite rules.
-/
private theorem isDat_M {c s t : K} (hτ : τ ^ 2 - 4 ≠ 0) (hc : c ≠ 0) (hs : Δ * s ^ 2 ≠ 0) (ht : t ≠ 0) {u : Etau K τ} (hu2 : u ^ 2 = -ω)
    (hu : QuadraticAlgebra.norm u = 1) {ν : Lsq K Δ} (hν : QuadraticAlgebra.norm ν = -1) :
    IsDat c (ν • ofE Δ u) ((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) := by
  have e1 := congrArg QuadraticAlgebra.re hu2
  have e2 := congrArg QuadraticAlgebra.im hu2
  simp [pow_two] at e1 e2
  simp [QuadraticAlgebra.norm] at hu hν
  have hΔ : Δ ≠ 0 := left_ne_zero_of_mul hs
  have hs0 : s ≠ 0 := fun h => hs (by simp [h])
  have hdd : (ν • ofE Δ u) * star (sigL (ν • ofE Δ u)) = -1 := by
    ext <;> simp [sigL, ofE]
    · linear_combination (u.re * u.re + τ * u.re * u.im + u.im * u.im) * hν - hu
    all_goals ring
  have hsm : sigL ((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) =
      -((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) := by
    ext <;> simp [sigL, ofE] <;> ring
  have hmm : ((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) *
      ((algebraMap K (Lsq K Δ) (t ^ 2 * (Δ * s ^ 2) * (τ ^ 2 - 4))⁻¹) •
        ((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ))) = 1 := by
    ext <;> simp [ofE]
    · field_simp
      ring
    all_goals ring
  refine ⟨hτ, hc, ?_, ⟨⟨_, _, hmm, by rw [mul_comm]; exact hmm⟩, rfl⟩, ?_, ?_⟩
  · ext <;> simp [sigL, ofE]
    · linear_combination (ν.re * ν.re - Δ * ν.im * ν.im) * e1
    · ring
    · linear_combination (u.re * u.im + u.im * u.re + τ * u.im * u.im) * hν - e2
    · ring
  · ext <;> simp [sigL, ofE] <;> ring
  · rw [hsm, mul_assoc, hdd]
    simp

/- English proof (translation)
Take `⟨o, rfl⟩` from `hk`. Rewrite `ha`, the goal using `[h.dual]`. Introduce `x hx`. Take `⟨r, hr⟩` from `ha x hx`. Use `⟨o * r, ?_⟩` and prove the remaining obligations.

Establish `e : (x * star ((algebraMap O K o) • a)).im = algebraMap O K o * (x * star a).im`. Simplify using `[Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, hr, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem fixP_smul {T : K} {S : Set (Etau K τ)} (h : IsFixP O τ T S) {k : K} (hk : k ∈ (algebraMap O K).range)
    {a : Etau K τ} (ha : a ∈ S) : k • a ∈ S := by
  obtain ⟨o, rfl⟩ := hk
  rw [h.dual] at ha ⊢
  intro x hx
  obtain ⟨r, hr⟩ := ha x hx
  refine ⟨o * r, ?_⟩
  have e : (x * star ((algebraMap O K o) • a)).im = algebraMap O K o * (x * star a).im := by
    simp [Algebra.smul_def]
    ring
  rw [map_mul, hr, e]
  ring

/- English proof (translation)
Rewrite `ha`, `hb`, the goal using `[h.dual]`. Introduce `x hx`. Take `⟨r, hr⟩` from `ha x hx`. Take `⟨r', hr'⟩` from `hb x hx`. Use `⟨r - r', ?_⟩` and prove the remaining obligations.

Establish `e : (x * star (a - b)).im = (x * star a).im - (x * star b).im`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_sub, hr, hr', e]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem fixP_sub {T : K} {S : Set (Etau K τ)} (h : IsFixP O τ T S)
    {a b : Etau K τ} (ha : a ∈ S) (hb : b ∈ S) : a - b ∈ S := by
  rw [h.dual] at ha hb ⊢
  intro x hx
  obtain ⟨r, hr⟩ := ha x hx
  obtain ⟨r', hr'⟩ := hb x hx
  refine ⟨r - r', ?_⟩
  have e : (x * star (a - b)).im = (x * star a).im - (x * star b).im := by
    simp
    ring
  rw [map_sub, hr, hr', e]
  ring

/- English proof (translation)
Rewrite using `[h.dual]`. Introduce `x _`. Conclude with `⟨0, by simp⟩`.
-/
private theorem fixP_zero {T : K} {S : Set (Etau K τ)} (h : IsFixP O τ T S) : (0 : Etau K τ) ∈ S := by
  rw [h.dual]
  intro x _
  exact ⟨0, by simp⟩

/- English proof (translation)
Establish `add : ∀ {p q : Etau K τ}, p ∈ S → q ∈ S → p + q ∈ S`. Introduce `p q hp hq`. Use `fixP_sub h hp (fixP_sub h (fixP_zero h) hq)` as an intermediate fact. Simplify using `using this`. Establish `e : v * a = v.re • a + v.im • (ω * a)`.

Apply the tactic sequence `ext <;> simp <;> ring`. Rewrite using `[e]`. Conclude with `add (fixP_smul h h1 ha) (fixP_smul h h2 (h.stab a ha))`.
-/
private theorem fixP_mul {T : K} {S : Set (Etau K τ)} (h : IsFixP O τ T S) {v : Etau K τ} (h1 : v.re ∈ (algebraMap O K).range)
    (h2 : v.im ∈ (algebraMap O K).range) {a : Etau K τ} (ha : a ∈ S) : v * a ∈ S := by
  have add : ∀ {p q : Etau K τ}, p ∈ S → q ∈ S → p + q ∈ S := by
    intro p q hp hq
    have := fixP_sub h hp (fixP_sub h (fixP_zero h) hq)
    simpa using this
  have e : v * a = v.re • a + v.im • (ω * a) := by
    ext <;> simp <;> ring
  rw [e]
  exact add (fixP_smul h h1 ha) (fixP_smul h h2 (h.stab a ha))

/- English proof (translation)
Establish `key : ∀ {A B : Set (Etau K τ)} {TA TB : K}, IsFixP O τ TA A → IsFixP O τ TB B → Phi O Δ g s A = Phi O Δ g s B → A ⊆ B`. Introduce `A B TA TB hA hB e a ha`. Establish `hmem : ((0 : Lsq K Δ), cmb Δ s a 0) ∈ Phi O Δ g s A` using `⟨by simp [IsInt, isIntegral_zero], a, ha, 0, fixP_zero hA, rfl⟩`. Rewrite `hmem` using `[e]`. Take `⟨_, a', ha', b', _, hab⟩` from `hmem`.

Rewrite using `[cmb_inj hab]`. Conclude with `ha'`. Conclude with `Set.Subset.antisymm (key h h' e) (key h' h e.symm)`.
-/
private theorem phi_inj {g s T T' : K} {S S' : Set (Etau K τ)} (h : IsFixP O τ T S) (h' : IsFixP O τ T' S')
    (e : Phi O Δ g s S = Phi O Δ g s S') : S = S' := by
  have key : ∀ {A B : Set (Etau K τ)} {TA TB : K}, IsFixP O τ TA A → IsFixP O τ TB B →
      Phi O Δ g s A = Phi O Δ g s B → A ⊆ B := by
    intro A B TA TB hA hB e a ha
    have hmem : ((0 : Lsq K Δ), cmb Δ s a 0) ∈ Phi O Δ g s A :=
      ⟨by simp [IsInt, isIntegral_zero], a, ha, 0, fixP_zero hA, rfl⟩
    rw [e] at hmem
    obtain ⟨_, a', ha', b', _, hab⟩ := hmem
    rw [cmb_inj hab]
    exact ha'
  exact Set.Subset.antisymm (key h h' e) (key h' h e.symm)

variable [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Use `haveI := L.frac`. Establish `e1` using `congrArg QuadraticAlgebra.re hu2`. Establish `e2` using `congrArg QuadraticAlgebra.im hu2`. Simplify using `[sq] at e1 e2`. Simplify using `[QuadraticAlgebra.norm] at hu`.

Take `⟨v, hv⟩` from `h2`. Establish `two : (2 : K) ≠ 0`. Introduce `h0`. Use `L.two.map (algebraMap O K)` as an intermediate fact. Rewrite `this` using `[map_ofNat, h0]`.

Conclude with `not_isUnit_zero this`. Establish `hre : u.re = -u.im`. Establish `hf : (u.re - u.im) * (u.re + u.im) = 0` using `by linear_combination e1`. Break down `mul_eq_zero.1 hf with h | h` into its components or cases. It suffices to derive a contradiction.

Establish `h' : u.re = u.im` using `by linear_combination h`. Rewrite `e2`, `hu` using `[h']`. Apply `two` to reduce the goal to its premises. Take the linear combination `e2 - hu`. Take the linear combination `h`.

Establish `hsq : u.im ^ 2 = algebraMap O K ↑v⁻¹`. Rewrite `hu` using `[hre]`. Establish `hv0 : algebraMap O K ↑v * algebraMap O K ↑v⁻¹ = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Rewrite `hv0` using `[hv]`.

Take the linear combination `(algebraMap O K ↑v⁻¹) * hu - u.im ^ 2 * hv0`. Establish `hint : IsIntegral O u.im`. Use `IsIntegral.of_pow two_pos ?_` and prove the remaining obligations. Rewrite using `[hsq]`. Conclude with `isIntegral_algebraMap`.

Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := O) (K := K)).1 hint`. Conclude with `⟨⟨-y, by rw [map_neg, hy, hre]⟩, ⟨y, hy⟩⟩`.
-/
private theorem u_int (L : IsLoc O Δ) (h2 : ∃ u : Oˣ, algebraMap O K u = 2 - τ) {u : Etau K τ} (hu2 : u ^ 2 = -ω)
    (hu : QuadraticAlgebra.norm u = 1) : u.re ∈ (algebraMap O K).range ∧ u.im ∈ (algebraMap O K).range := by
  haveI := L.frac
  have e1 := congrArg QuadraticAlgebra.re hu2
  have e2 := congrArg QuadraticAlgebra.im hu2
  simp [sq] at e1 e2
  simp [QuadraticAlgebra.norm] at hu
  obtain ⟨v, hv⟩ := h2
  have two : (2 : K) ≠ 0 := by
    intro h0
    have := L.two.map (algebraMap O K)
    rw [map_ofNat, h0] at this
    exact not_isUnit_zero this
  have hre : u.re = -u.im := by
    have hf : (u.re - u.im) * (u.re + u.im) = 0 := by linear_combination e1
    rcases mul_eq_zero.1 hf with h | h
    · exfalso
      have h' : u.re = u.im := by linear_combination h
      rw [h'] at e2 hu
      apply two
      linear_combination e2 - hu
    · linear_combination h
  have hsq : u.im ^ 2 = algebraMap O K ↑v⁻¹ := by
    rw [hre] at hu
    have hv0 : algebraMap O K ↑v * algebraMap O K ↑v⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hv] at hv0
    linear_combination (algebraMap O K ↑v⁻¹) * hu - u.im ^ 2 * hv0
  have hint : IsIntegral O u.im := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hsq]
    exact isIntegral_algebraMap
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := K)).1 hint
  exact ⟨⟨-y, by rw [map_neg, hy, hre]⟩, ⟨y, hy⟩⟩

/- English proof (translation)
Introduce and unpack `⟨x1, x2⟩ ⟨hx1, a, ha, b, hb, hx2⟩`. Take `⟨hp, q, hq⟩` from `((descent O K Δ L s ε hs ν).1).1 hν`. Establish `hνe : ν = ⟨ν.re, s * algebraMap O K q⟩`. Use `ext`. Both sides reduce to the same expression.

Conclude with `hq`. Simplify using `only at hx2 hx1`. Substitute `hx2` using the available equality. Rewrite using `[hνe, semi_cmb]`. Establish `hva` using `fixP_mul h h1 h2 ha`.

Establish `hvb` using `fixP_mul h h1 h2 hb`. Establish `hq' : algebraMap O K q ∈ (algebraMap O K).range` using `⟨q, rfl⟩`. Establish `hD : Δ * s ^ 2 * algebraMap O K q ∈ (algebraMap O K).range` using `⟨ε * q, by rw [map_mul, hs]⟩`. Simplify using `only [Phi, Set.mem_setOf_eq]`. Use `⟨?_, _, fixP_sub h (fixP_smul h hp hva) (fixP_smul h hD hvb), _, fixP_sub h (fixP_smul h hq' hva) (fixP_smul h hp hvb), rfl⟩` and prove the remaining obligations.

Establish `hst` using `(descent O K Δ L s ε hs (g • x1)).2 hx1`. Establish `e : star (g • x1) = g • star x1`. Apply the tactic sequence `ext <;> simp`. Rewrite `hst` using `[e]`. Conclude with `hst`.
-/
private theorem phi_semi (L : IsLoc O Δ) {g s T : K} {ε : Oˣ} (hs : Δ * s ^ 2 = algebraMap O K ε) {S : Set (Etau K τ)}
    (h : IsFixP O τ T S) {v : Etau K τ} (h1 : v.re ∈ (algebraMap O K).range) (h2 : v.im ∈ (algebraMap O K).range)
    {ν : Lsq K Δ} (hν : IsInt O ν) : ∀ x ∈ Phi O Δ g s S, semi (ν • ofE Δ v) x ∈ Phi O Δ g s S := by
  rintro ⟨x1, x2⟩ ⟨hx1, a, ha, b, hb, hx2⟩
  obtain ⟨hp, q, hq⟩ := ((descent O K Δ L s ε hs ν).1).1 hν
  have hνe : ν = ⟨ν.re, s * algebraMap O K q⟩ := by
    ext
    · rfl
    · exact hq
  simp only at hx2 hx1
  subst hx2
  rw [hνe, semi_cmb]
  have hva := fixP_mul h h1 h2 ha
  have hvb := fixP_mul h h1 h2 hb
  have hq' : algebraMap O K q ∈ (algebraMap O K).range := ⟨q, rfl⟩
  have hD : Δ * s ^ 2 * algebraMap O K q ∈ (algebraMap O K).range := ⟨ε * q, by rw [map_mul, hs]⟩
  simp only [Phi, Set.mem_setOf_eq]
  refine ⟨?_, _, fixP_sub h (fixP_smul h hp hva) (fixP_smul h hD hvb), _,
    fixP_sub h (fixP_smul h hq' hva) (fixP_smul h hp hvb), rfl⟩
  have hst := (descent O K Δ L s ε hs (g • x1)).2 hx1
  have e : star (g • x1) = g • star x1 := by
    ext <;> simp
  rw [e] at hst
  exact hst

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [cmb] <;> ring`.
-/
private theorem cmb_add' (s : K) (a b a' b' : Etau K τ) :
    cmb Δ s a b + cmb Δ s a' b' = cmb Δ s (a + a') (b + b') := by
  ext <;> simp [cmb] <;> ring

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [cmb] <;> simp only [Algebra.smul_def] <;> ring`.
-/
private theorem smul_cmb (r : O) (s : K) (a b : Etau K τ) :
    r • cmb Δ s a b = cmb Δ s (r • a) (r • b) := by
  ext <;> simp [cmb] <;> simp only [Algebra.smul_def] <;> ring

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [cmb]`.
-/
private theorem cmb_zero' (s : K) : cmb Δ s (0 : Etau K τ) 0 = 0 := by
  ext <;> simp [cmb]

/- English proof (translation)
Take `⟨F0, hF0⟩` from `h.fg`. Establish `hmS : ∀ {a : Etau K τ}, a ∈ S ↔ a ∈ Submodule.span O (F0 : Set (Etau K τ))`. Introduce `a`. Rewrite using `[hF0]`. Both sides reduce to the same expression.

Establish `hsne : s ≠ 0`. Introduce and unpack `rfl`. Establish `hne : (algebraMap O K ε : K) ≠ 0` using `(ε.isUnit.map (algebraMap O K)).ne_zero`. Conclude with `hne (by simpa using hs.symm)`. Set `P : Submodule O (Sp Δ τ)` to `{ carrier := Phi O Δ g s S add_mem' := by`.

Introduce and unpack `x y ⟨hx1, a, ha, b, hb, hx2⟩ ⟨hy1, a', ha', b', hb', hy2⟩`. Use `⟨?_, a + a', ?_, b + b', ?_, ?_⟩` and prove the remaining obligations. Use `show IsIntegral O (g • (x.1 + y.1))`. Rewrite using `[smul_add]`. Conclude with `IsIntegral.add hx1 hy1`.

Conclude with `hmS.2 (add_mem (hmS.1 ha) (hmS.1 ha'))`. Conclude with `hmS.2 (add_mem (hmS.1 hb) (hmS.1 hb'))`. Use `show x.2 + y.2 = _`. Rewrite using `[hx2, hy2, cmb_add']`. Use the proof step `zero_mem' := by`.

Use `⟨?_, 0, hmS.2 (zero_mem _), 0, hmS.2 (zero_mem _), ?_⟩` and prove the remaining obligations. Use `show IsIntegral O (g • (0 : Lsq K Δ))`. Rewrite using `[smul_zero]`. Conclude with `isIntegral_zero`. Use `show (0 : EL Δ τ) = _`.

Rewrite using `[cmb_zero']`. Use the proof step `smul_mem' := by`. Introduce and unpack `r x ⟨hx1, a, ha, b, hb, hx2⟩`. Use `⟨?_, r • a, hmS.2 (Submodule.smul_mem _ r (hmS.1 ha)), r • b, hmS.2 (Submodule.smul_mem _ r (hmS.1 hb)), ?_⟩` and prove the remaining obligations. Use `show IsIntegral O (g • (r • x.1))`.

Establish `e : g • (r • x.1) = algebraMap O (Lsq K Δ) r * (g • x.1)`. Rewrite using `[Algebra.smul_def r x.1, Algebra.smul_def g, Algebra.smul_def g]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `isIntegral_algebraMap.mul hx1`.

Use `show r • x.2 = _`. Rewrite using `[hx2, smul_cmb] }`. Set `F : Finset (Sp Δ τ)` to `({(algebraMap K (Lsq K Δ) g⁻¹, 0), (⟨0, g⁻¹ * s⟩, 0)} : Finset (Sp Δ τ)) ∪ F0.image (fun a => ((0 : Lsq K Δ), cmb Δ s a 0)) ∪ F0.image (fun b => ((0 : Lsq K Δ), cmb Δ s 0 b))`. Use `⟨F, ?_⟩` and prove the remaining obligations. Establish `key : P = Submodule.span O (F : Set (Sp Δ τ))`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨hx1, a, ha, b, hb, hx2⟩`. Establish `hA : ∀ a ∈ Submodule.span O (F0 : Set (Etau K τ)), ((0 : Lsq K Δ), cmb Δ s a 0) ∈ Submodule.span O (F : Set (Sp Δ τ))`. Introduce `a ha`. Proceed by induction on `ha using Submodule.span_induction with`.

Consider the case `mem y hy`. Apply `Submodule.subset_span` to reduce the goal to its premises. Simplify using `only [F, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image]`. Conclude with `Or.inl (Or.inr ⟨y, hy, rfl⟩)`. Consider the case `zero`.

Rewrite using `[cmb_zero']`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz`. Establish `e : ((0 : Lsq K Δ), cmb Δ s (y + z) 0) = ((0 : Lsq K Δ), cmb Δ s y 0) + ((0 : Lsq K Δ), cmb Δ s z 0)`. Rewrite using `[Prod.mk_add_mk, cmb_add', add_zero, add_zero]`.

Rewrite using `[e]`. Conclude with `add_mem hy hz`. Consider the case `smul r y _ hy`. Establish `e : ((0 : Lsq K Δ), cmb Δ s (r • y) 0) = r • ((0 : Lsq K Δ), cmb Δ s y 0)`. Rewrite using `[Prod.smul_mk, smul_cmb, smul_zero, smul_zero]`.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ r hy`. Establish `hB : ∀ b ∈ Submodule.span O (F0 : Set (Etau K τ)), ((0 : Lsq K Δ), cmb Δ s 0 b) ∈ Submodule.span O (F : Set (Sp Δ τ))`. Introduce `b hb`. Proceed by induction on `hb using Submodule.span_induction with`.

Consider the case `mem y hy`. Apply `Submodule.subset_span` to reduce the goal to its premises. Simplify using `only [F, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image]`. Conclude with `Or.inr ⟨y, hy, rfl⟩`. Consider the case `zero`.

Rewrite using `[cmb_zero']`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz`. Establish `e : ((0 : Lsq K Δ), cmb Δ s 0 (y + z)) = ((0 : Lsq K Δ), cmb Δ s 0 y) + ((0 : Lsq K Δ), cmb Δ s 0 z)`. Rewrite using `[Prod.mk_add_mk, cmb_add', add_zero, add_zero]`.

Rewrite using `[e]`. Conclude with `add_mem hy hz`. Consider the case `smul r y _ hy`. Establish `e : ((0 : Lsq K Δ), cmb Δ s 0 (r • y)) = r • ((0 : Lsq K Δ), cmb Δ s 0 y)`. Rewrite using `[Prod.smul_mk, smul_cmb, smul_zero, smul_zero]`.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ r hy`. Take `⟨⟨r, hr⟩, b', hb'⟩` from `((descent O K Δ L s ε hs (g • x.1)).1).1 hx1`. Establish `hx : x = (r • ((algebraMap K (Lsq K Δ) g⁻¹, 0) : Sp Δ τ) + b' • ((⟨0, g⁻¹ * s⟩, 0) : Sp Δ τ)) + (((0 : Lsq K Δ), cmb Δ s a 0) + ((0 : Lsq K Δ), cmb Δ s 0 b))`. Take `⟨x1, x2⟩` from `x`.

Simplify using `only at hx2 hr hb'`. Establish `hr' : x1.re = g⁻¹ * algebraMap O K r`. Rewrite using `[hr]`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.

Establish `hb'' : x1.im = g⁻¹ * (s * algebraMap O K b')`. Establish `e2 : (g • x1).im = g * x1.im` using `by simp`. Rewrite `hb'` using `[e2]`. Rewrite using `[← hb']`. Clear the denominators using the available nonvanishing facts.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `ext`. Simplify using the standard rewrite rules. Simplify using `only [Algebra.smul_def]`. Rewrite using `[hr']`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Simplify using `only [Algebra.smul_def]`. Rewrite using `[hb'']`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add]`. Rewrite using `[hx2, cmb_add', add_zero, zero_add]`. Rewrite using `[hx]`. Use `add_mem (add_mem (Submodule.smul_mem _ r (Submodule.subset_span ?_)) (Submodule.smul_mem _ b' (Submodule.subset_span ?_))) (add_mem (hA a (hmS.1 ha)) (hB b (hmS.1 hb)))` and prove the remaining obligations. Simplify using `[F]`.

Simplify using `[F]`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Simplify using `only [F, Finset.coe_union, Finset.coe_image, Finset.coe_insert, Finset.coe_singleton, Set.mem_union, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff] at hx`. Break down `hx with ((rfl | rfl) | ⟨a, ha, rfl⟩) | ⟨b, hb, rfl⟩` into its components or cases.

Use `⟨?_, 0, hmS.2 (zero_mem _), 0, hmS.2 (zero_mem _), (cmb_zero' s).symm⟩ show IsIntegral O (g • algebraMap K (Lsq K Δ) g⁻¹)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hg, map_one]`. Conclude with `isIntegral_one`. Use `⟨?_, 0, hmS.2 (zero_mem _), 0, hmS.2 (zero_mem _), (cmb_zero' s).symm⟩` and prove the remaining obligations. Use `((descent O K Δ L s ε hs _).1).2 ⟨⟨0, by simp⟩, 1, ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Conclude with `⟨by show IsIntegral O (g • (0 : Lsq K Δ)); rw [smul_zero]; exact isIntegral_zero, a, hmS.2 (Submodule.subset_span ha), 0, hmS.2 (zero_mem _), rfl⟩`. Conclude with `⟨by show IsIntegral O (g • (0 : Lsq K Δ)); rw [smul_zero]; exact isIntegral_zero, 0, hmS.2 (zero_mem _), b, hmS.2 (Submodule.subset_span hb), rfl⟩`. Conclude with `congrArg (fun Q : Submodule O (Sp Δ τ) => (Q : Set (Sp Δ τ))) key`.
-/
private theorem phi_fg (L : IsLoc O Δ) {g s T : K} (hg : g ≠ 0) {ε : Oˣ} (hs : Δ * s ^ 2 = algebraMap O K ε) {S : Set (Etau K τ)}
    (h : IsFixP O τ T S) : ∃ F : Finset (Sp Δ τ), Phi O Δ g s S = Submodule.span O (F : Set (Sp Δ τ)) := by
  classical
  obtain ⟨F0, hF0⟩ := h.fg
  have hmS : ∀ {a : Etau K τ}, a ∈ S ↔ a ∈ Submodule.span O (F0 : Set (Etau K τ)) := by
    intro a
    rw [hF0]
    rfl
  have hsne : s ≠ 0 := by
    rintro rfl
    have hne : (algebraMap O K ε : K) ≠ 0 := (ε.isUnit.map (algebraMap O K)).ne_zero
    exact hne (by simpa using hs.symm)
  let P : Submodule O (Sp Δ τ) :=
    { carrier := Phi O Δ g s S
      add_mem' := by
        rintro x y ⟨hx1, a, ha, b, hb, hx2⟩ ⟨hy1, a', ha', b', hb', hy2⟩
        refine ⟨?_, a + a', ?_, b + b', ?_, ?_⟩
        · show IsIntegral O (g • (x.1 + y.1))
          rw [smul_add]
          exact IsIntegral.add hx1 hy1
        · exact hmS.2 (add_mem (hmS.1 ha) (hmS.1 ha'))
        · exact hmS.2 (add_mem (hmS.1 hb) (hmS.1 hb'))
        · show x.2 + y.2 = _
          rw [hx2, hy2, cmb_add']
      zero_mem' := by
        refine ⟨?_, 0, hmS.2 (zero_mem _), 0, hmS.2 (zero_mem _), ?_⟩
        · show IsIntegral O (g • (0 : Lsq K Δ))
          rw [smul_zero]
          exact isIntegral_zero
        · show (0 : EL Δ τ) = _
          rw [cmb_zero']
      smul_mem' := by
        rintro r x ⟨hx1, a, ha, b, hb, hx2⟩
        refine ⟨?_, r • a, hmS.2 (Submodule.smul_mem _ r (hmS.1 ha)), r • b,
          hmS.2 (Submodule.smul_mem _ r (hmS.1 hb)), ?_⟩
        · show IsIntegral O (g • (r • x.1))
          have e : g • (r • x.1) = algebraMap O (Lsq K Δ) r * (g • x.1) := by
            rw [Algebra.smul_def r x.1, Algebra.smul_def g, Algebra.smul_def g]
            ring
          rw [e]
          exact isIntegral_algebraMap.mul hx1
        · show r • x.2 = _
          rw [hx2, smul_cmb] }
  let F : Finset (Sp Δ τ) :=
    ({(algebraMap K (Lsq K Δ) g⁻¹, 0), (⟨0, g⁻¹ * s⟩, 0)} : Finset (Sp Δ τ)) ∪
      F0.image (fun a => ((0 : Lsq K Δ), cmb Δ s a 0)) ∪
      F0.image (fun b => ((0 : Lsq K Δ), cmb Δ s 0 b))
  refine ⟨F, ?_⟩
  have key : P = Submodule.span O (F : Set (Sp Δ τ)) := by
    apply le_antisymm
    · rintro x ⟨hx1, a, ha, b, hb, hx2⟩
      have hA : ∀ a ∈ Submodule.span O (F0 : Set (Etau K τ)),
          ((0 : Lsq K Δ), cmb Δ s a 0) ∈ Submodule.span O (F : Set (Sp Δ τ)) := by
        intro a ha
        induction ha using Submodule.span_induction with
        | mem y hy =>
          apply Submodule.subset_span
          simp only [F, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image]
          exact Or.inl (Or.inr ⟨y, hy, rfl⟩)
        | zero =>
          rw [cmb_zero']
          exact zero_mem _
        | add y z _ _ hy hz =>
          have e : ((0 : Lsq K Δ), cmb Δ s (y + z) 0) = ((0 : Lsq K Δ), cmb Δ s y 0) + ((0 : Lsq K Δ), cmb Δ s z 0) := by
            rw [Prod.mk_add_mk, cmb_add', add_zero, add_zero]
          rw [e]
          exact add_mem hy hz
        | smul r y _ hy =>
          have e : ((0 : Lsq K Δ), cmb Δ s (r • y) 0) = r • ((0 : Lsq K Δ), cmb Δ s y 0) := by
            rw [Prod.smul_mk, smul_cmb, smul_zero, smul_zero]
          rw [e]
          exact Submodule.smul_mem _ r hy
      have hB : ∀ b ∈ Submodule.span O (F0 : Set (Etau K τ)),
          ((0 : Lsq K Δ), cmb Δ s 0 b) ∈ Submodule.span O (F : Set (Sp Δ τ)) := by
        intro b hb
        induction hb using Submodule.span_induction with
        | mem y hy =>
          apply Submodule.subset_span
          simp only [F, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image]
          exact Or.inr ⟨y, hy, rfl⟩
        | zero =>
          rw [cmb_zero']
          exact zero_mem _
        | add y z _ _ hy hz =>
          have e : ((0 : Lsq K Δ), cmb Δ s 0 (y + z)) = ((0 : Lsq K Δ), cmb Δ s 0 y) + ((0 : Lsq K Δ), cmb Δ s 0 z) := by
            rw [Prod.mk_add_mk, cmb_add', add_zero, add_zero]
          rw [e]
          exact add_mem hy hz
        | smul r y _ hy =>
          have e : ((0 : Lsq K Δ), cmb Δ s 0 (r • y)) = r • ((0 : Lsq K Δ), cmb Δ s 0 y) := by
            rw [Prod.smul_mk, smul_cmb, smul_zero, smul_zero]
          rw [e]
          exact Submodule.smul_mem _ r hy
      obtain ⟨⟨r, hr⟩, b', hb'⟩ := ((descent O K Δ L s ε hs (g • x.1)).1).1 hx1
      have hx : x = (r • ((algebraMap K (Lsq K Δ) g⁻¹, 0) : Sp Δ τ) + b' • ((⟨0, g⁻¹ * s⟩, 0) : Sp Δ τ)) +
          (((0 : Lsq K Δ), cmb Δ s a 0) + ((0 : Lsq K Δ), cmb Δ s 0 b)) := by
        obtain ⟨x1, x2⟩ := x
        simp only at hx2 hr hb'
        have hr' : x1.re = g⁻¹ * algebraMap O K r := by
          rw [hr]
          simp
          field_simp
        have hb'' : x1.im = g⁻¹ * (s * algebraMap O K b') := by
          have e2 : (g • x1).im = g * x1.im := by simp
          rw [e2] at hb'
          rw [← hb']
          field_simp
        refine Prod.ext ?_ ?_
        · ext
          · simp
            simp only [Algebra.smul_def]
            rw [hr']
            ring
          · simp
            simp only [Algebra.smul_def]
            rw [hb'']
            ring
        · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add]
          rw [hx2, cmb_add', add_zero, zero_add]
      rw [hx]
      refine add_mem (add_mem (Submodule.smul_mem _ r (Submodule.subset_span ?_))
        (Submodule.smul_mem _ b' (Submodule.subset_span ?_))) (add_mem (hA a (hmS.1 ha)) (hB b (hmS.1 hb)))
      · simp [F]
      · simp [F]
    · rw [Submodule.span_le]
      intro x hx
      simp only [F, Finset.coe_union, Finset.coe_image, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_union, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with ((rfl | rfl) | ⟨a, ha, rfl⟩) | ⟨b, hb, rfl⟩
      · refine ⟨?_, 0, hmS.2 (zero_mem _), 0, hmS.2 (zero_mem _), (cmb_zero' s).symm⟩
        show IsIntegral O (g • algebraMap K (Lsq K Δ) g⁻¹)
        rw [Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hg, map_one]
        exact isIntegral_one
      · refine ⟨?_, 0, hmS.2 (zero_mem _), 0, hmS.2 (zero_mem _), (cmb_zero' s).symm⟩
        refine ((descent O K Δ L s ε hs _).1).2 ⟨⟨0, by simp⟩, 1, ?_⟩
        simp
        field_simp
      · exact ⟨by show IsIntegral O (g • (0 : Lsq K Δ)); rw [smul_zero]; exact isIntegral_zero,
          a, hmS.2 (Submodule.subset_span ha), 0, hmS.2 (zero_mem _), rfl⟩
      · exact ⟨by show IsIntegral O (g • (0 : Lsq K Δ)); rw [smul_zero]; exact isIntegral_zero,
          0, hmS.2 (zero_mem _), b, hmS.2 (Submodule.subset_span hb), rfl⟩
  exact congrArg (fun Q : Submodule O (Sp Δ τ) => (Q : Set (Sp Δ τ))) key

/- English proof (translation)
Establish `hε0 : algebraMap O K (ε : O) ≠ 0` using `(ε.isUnit.map (algebraMap O K)).ne_zero`. Establish `hη0 : algebraMap O K (η : O) ≠ 0` using `(η.isUnit.map (algebraMap O K)).ne_zero`. Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`. Apply `hε0` to reduce the goal to its premises.

Rewrite using `[← hs]`. Expand and normalize the polynomial expressions, which then agree. Establish `D` using `fun x => descent O K Δ L s ε hs x`. Use `⟨phi_fg L hg hs h, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y1, y2⟩`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy1, a', ha', b', hb', hy2⟩ ⟨x1, x2⟩ ⟨hx1, a, ha, b, hb, hx2⟩`. Simplify using `only at hy2 hx2 hy1 hx1 ⊢`. Substitute `hy2 hx2` using the available equality. Rewrite using `[herm_cmb]`.

Apply `IsIntegral.add` to reduce the goal to its premises. Establish `e : c • (x1 * star y1) = (η : O) • ((g • x1) * star (g • y1))`. Rewrite using `[hc]`. Apply the tactic sequence `ext <;> simp <;> simp only [Algebra.smul_def] <;> ring`. Rewrite using `[e]`.

Conclude with `IsIntegral.smul _ (IsIntegral.mul hx1 ((D _).2 hy1))`. Take `⟨r1, hr1⟩` from `(h.dual a').1 ha' b hb`. Take `⟨r2, hr2⟩` from `(h.dual b').1 hb' a ha`. Take `⟨r3, hr3⟩` from `(h.dual a').1 ha' a ha`. Take `⟨r4, hr4⟩` from `(h.dual b').1 hb' b hb`.

Use `(D _).1.2 ⟨⟨ε * (r1 - r2), ?_⟩, ⟨r3 - ε * r4, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_sub, hr1, hr2, hs]`. Simplify using `only [map_mul, map_sub, hr3, hr4, hs]`. Introduce `H`. Take `⟨a', b', rfl⟩` from `cmb_ex hs0 y2`.

Use `⟨?_, a', ?_, b', ?_, rfl⟩` and prove the remaining obligations. Establish `hw` using `H ((g⁻¹ • (1 : Lsq K Δ)), cmb Δ s 0 0) ⟨by simpa [hg] using (isIntegral_one : IsIntegral O (1 : Lsq K Δ)), 0, fixP_zero h, 0, fixP_zero h, rfl⟩`. Rewrite `hw` using `[herm_cmb]`. Generalize the expression as in `hW : c • (g⁻¹ • (1 : Lsq K Δ) * star y1) + _ = W at hw`. Establish `e : g • y1 = ((η⁻¹ : Oˣ) : O) • star W`.

Rewrite using `[← hW]`. Apply the tactic sequence `ext <;> simp [hc] <;> simp only [Algebra.smul_def, map_units_inv] <;> field_simp <;> ring`. Rewrite using `[e]`. Conclude with `IsIntegral.smul _ ((D _).2 hw)`. Rewrite using `[h.dual]`.

Introduce `a ha`. Establish `hw` using `H (0, cmb Δ s a 0) ⟨by simpa using (isIntegral_zero : IsIntegral O (0 : Lsq K Δ)), a, ha, 0, fixP_zero h, rfl⟩`. Rewrite `hw` using `[herm_cmb]`. Take `⟨_, o, ho⟩` from `(D _).1.1 hw`. Use `⟨o, ?_⟩` and prove the remaining obligations.

Simplify using `[hs0] at ho`. Rewrite using `[← ho]`. Apply the tactic sequence `simp <;> ring`. Rewrite using `[h.dual]`. Introduce `b hb`.

Establish `hw` using `H (0, cmb Δ s b 0) ⟨by simpa using (isIntegral_zero : IsIntegral O (0 : Lsq K Δ)), b, hb, 0, fixP_zero h, rfl⟩`. Rewrite `hw` using `[herm_cmb]`. Take `⟨⟨o, ho⟩, _⟩` from `(D _).1.1 hw`. Simplify using `at ho`. Use `⟨-(((ε⁻¹ : Oˣ) : O) * o), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_neg, map_mul, ho, hs, map_units_inv]`. Establish `hX : (b * star b').im = -(b.re * b'.im) + b.im * (b'.re + τ * b'.im) + -(τ * b.im * b'.im)`. Apply the tactic sequence `simp <;> ring`. Rewrite using `[hX]`. Clear the denominators using the available nonvanishing facts.

Establish `hsu : (star u).re ∈ (algebraMap O K).range ∧ (star u).im ∈ (algebraMap O K).range`. Take `⟨a, ha⟩` from `h1`. Take `⟨b, hb⟩` from `h2`. Take `⟨c', hc'⟩` from `hτ`. Conclude with `⟨⟨a + c' * b, by simp [ha, hb, hc']⟩, ⟨-b, by simp [hb]⟩⟩`.

Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `phi_semi L hs h h1 h2 hν x hx`. Introduce `x hx`. Conclude with `⟨_, phi_semi L hs h hsu.1 hsu.2 hν.neg x hx, semi_inv hu hν' x⟩`.
-/
private theorem phi_fix (L : IsLoc O Δ) {c g s t : K} (hg : g ≠ 0) {η ε : Oˣ} (hc : c = algebraMap O K η * g ^ 2)
    (hs : Δ * s ^ 2 = algebraMap O K ε) {u : Etau K τ} (h1 : u.re ∈ (algebraMap O K).range) (h2 : u.im ∈ (algebraMap O K).range)
    (hτ : τ ∈ (algebraMap O K).range) (hu : QuadraticAlgebra.norm u = 1) {ν : Lsq K Δ} (hν : IsInt O ν)
    (hν' : QuadraticAlgebra.norm ν = -1) {S : Set (Etau K τ)} (h : IsFixP O τ (t * (τ ^ 2 - 4)) S) :
    IsFix O c (ν • ofE Δ u) ((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) (Phi O Δ g s S) := by
  have hε0 : algebraMap O K (ε : O) ≠ 0 := (ε.isUnit.map (algebraMap O K)).ne_zero
  have hη0 : algebraMap O K (η : O) ≠ 0 := (η.isUnit.map (algebraMap O K)).ne_zero
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hε0
    rw [← hs]
    ring
  have D := fun x => descent O K Δ L s ε hs x
  refine ⟨phi_fg L hg hs h, ?_, ?_⟩
  · rintro ⟨y1, y2⟩
    constructor
    · rintro ⟨hy1, a', ha', b', hb', hy2⟩ ⟨x1, x2⟩ ⟨hx1, a, ha, b, hb, hx2⟩
      simp only at hy2 hx2 hy1 hx1 ⊢
      subst hy2 hx2
      rw [herm_cmb]
      apply IsIntegral.add
      · have e : c • (x1 * star y1) = (η : O) • ((g • x1) * star (g • y1)) := by
          rw [hc]
          ext <;> simp <;> simp only [Algebra.smul_def] <;> ring
        rw [e]
        exact IsIntegral.smul _ (IsIntegral.mul hx1 ((D _).2 hy1))
      · obtain ⟨r1, hr1⟩ := (h.dual a').1 ha' b hb
        obtain ⟨r2, hr2⟩ := (h.dual b').1 hb' a ha
        obtain ⟨r3, hr3⟩ := (h.dual a').1 ha' a ha
        obtain ⟨r4, hr4⟩ := (h.dual b').1 hb' b hb
        refine (D _).1.2 ⟨⟨ε * (r1 - r2), ?_⟩, ⟨r3 - ε * r4, ?_⟩⟩
        · simp only [map_mul, map_sub, hr1, hr2, hs]
        · simp only [map_mul, map_sub, hr3, hr4, hs]
    · intro H
      obtain ⟨a', b', rfl⟩ := cmb_ex hs0 y2
      refine ⟨?_, a', ?_, b', ?_, rfl⟩
      · have hw := H ((g⁻¹ • (1 : Lsq K Δ)), cmb Δ s 0 0)
          ⟨by simpa [hg] using (isIntegral_one : IsIntegral O (1 : Lsq K Δ)), 0, fixP_zero h, 0, fixP_zero h, rfl⟩
        rw [herm_cmb] at hw
        generalize hW : c • (g⁻¹ • (1 : Lsq K Δ) * star y1) + _ = W at hw
        have e : g • y1 = ((η⁻¹ : Oˣ) : O) • star W := by
          rw [← hW]
          ext <;> simp [hc] <;> simp only [Algebra.smul_def, map_units_inv] <;> field_simp <;> ring
        rw [e]
        exact IsIntegral.smul _ ((D _).2 hw)
      · rw [h.dual]
        intro a ha
        have hw := H (0, cmb Δ s a 0) ⟨by simpa using (isIntegral_zero : IsIntegral O (0 : Lsq K Δ)), a, ha, 0, fixP_zero h, rfl⟩
        rw [herm_cmb] at hw
        obtain ⟨_, o, ho⟩ := (D _).1.1 hw
        refine ⟨o, ?_⟩
        simp [hs0] at ho
        rw [← ho]
        simp <;> ring
      · rw [h.dual]
        intro b hb
        have hw := H (0, cmb Δ s b 0) ⟨by simpa using (isIntegral_zero : IsIntegral O (0 : Lsq K Δ)), b, hb, 0, fixP_zero h, rfl⟩
        rw [herm_cmb] at hw
        obtain ⟨⟨o, ho⟩, _⟩ := (D _).1.1 hw
        simp at ho
        refine ⟨-(((ε⁻¹ : Oˣ) : O) * o), ?_⟩
        rw [map_neg, map_mul, ho, hs, map_units_inv]
        have hX : (b * star b').im = -(b.re * b'.im) + b.im * (b'.re + τ * b'.im) + -(τ * b.im * b'.im) := by
          simp <;> ring
        rw [hX]
        field_simp
  · have hsu : (star u).re ∈ (algebraMap O K).range ∧ (star u).im ∈ (algebraMap O K).range := by
      obtain ⟨a, ha⟩ := h1
      obtain ⟨b, hb⟩ := h2
      obtain ⟨c', hc'⟩ := hτ
      exact ⟨⟨a + c' * b, by simp [ha, hb, hc']⟩, ⟨-b, by simp [hb]⟩⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact phi_semi L hs h h1 h2 hν x hx
    · intro x hx
      exact ⟨_, phi_semi L hs h hsu.1 hsu.2 hν.neg x hx, semi_inv hu hν' x⟩

/- English proof (translation)
Establish `hε0 : algebraMap O K ↑ε ≠ 0` using `(ε.isUnit.map (algebraMap O K)).ne_zero`. Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`. Apply `hε0` to reduce the goal to its premises. Rewrite using `[← hs]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hεε : algebraMap O K ↑ε * algebraMap O K ↑ε⁻¹ = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Establish `D` using `descent O K Δ L s ε hs`. Establish `hint : ∀ r : Lsq K Δ, r.re ∈ (algebraMap O K).range → (∃ b, r.im = s * algebraMap O K b) → IsInt O r` using `fun r e1 e2 => ((D r).1).2 ⟨e1, e2⟩`.

Take `⟨hadd, hsm, hfst, hmulv⟩` from `One.splitS O K Δ τ L hτ hτ' c _ _ hd S h`. Establish `hofE : ∀ v a : Etau K τ, ofE Δ v * ofE Δ a = ofE Δ (v * a)`. Introduce `v a`. Use `ofE_cmb (Δ := Δ) 1 v a 0` as an intermediate fact. Rewrite `this` using `[cmb_zero, mul_zero, cmb_zero]`.

Conclude with `this`. Establish `hz : ∀ r : Lsq K Δ, IsInt O r → ∀ y : EL Δ τ, ((0 : Lsq K Δ), y) ∈ S → ((0 : Lsq K Δ), r • y) ∈ S`. Introduce `r hr y hy`. Use `hsm _ hy r hr` as an intermediate fact. Simplify using `using this`.

Establish `hzadd : ∀ y y' : EL Δ τ, ((0 : Lsq K Δ), y) ∈ S → ((0 : Lsq K Δ), y') ∈ S → ((0 : Lsq K Δ), y + y') ∈ S`. Introduce `y y' hy hy'`. Use `hadd _ hy _ hy'` as an intermediate fact. Simplify using `using this`. Establish `hneg1 : IsInt O (-1 : Lsq K Δ)` using `hint _ ⟨-1, by simp⟩ ⟨0, by simp⟩`.

Establish `hsplit : ∀ x : Sp Δ τ, x ∈ S ↔ (x.1, (0 : EL Δ τ)) ∈ S ∧ ((0 : Lsq K Δ), x.2) ∈ S`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨hfst x hx, ?_⟩` and prove the remaining obligations.

Use `hadd _ hx _ (hsm _ (hfst x hx) (-1) hneg1)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Conclude with `Prod.ext (by simp) (by simp)`. Introduce and unpack `⟨e1, e2⟩`. Use `hadd _ e1 _ e2` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Conclude with `Prod.ext (by simp) (by simp)`. Establish `hus : (star u).re ∈ (algebraMap O K).range ∧ (star u).im ∈ (algebraMap O K).range`. Take `⟨a1, ha1⟩` from `h1`. Take `⟨b1, hb1⟩` from `h2`.

Take `⟨t1, ht1⟩` from `hτ`. Conclude with `⟨⟨a1 + t1 * b1, by simp [ha1, hb1, ht1]⟩, ⟨-b1, by simp [hb1]⟩⟩`. Establish `hνs : IsInt O (-star ν)` using `((D ν).2 hν).neg`. Establish `hid : ∀ w : EL Δ τ, (-star ν) • (ofE Δ (star u) * ((ν • ofE Δ u) * w)) = w`. Introduce `w`.

Establish `e1 : ofE Δ (star u) * ofE Δ u = 1`. Rewrite using `[hofE, mul_comm, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hu, map_one]`. Apply the tactic sequence `ext <;> simp [ofE]`. Establish `e2 : (-star ν) * ν = 1`. Rewrite using `[neg_mul, mul_comm, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hν']`.

Simplify using the standard rewrite rules. Rewrite using `[smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc, e1, one_mul, e2, one_smul]`. Establish `hsig : ∀ y : EL Δ τ, ((0 : Lsq K Δ), y) ∈ S → ((0 : Lsq K Δ), sigL y) ∈ S`. Introduce `y hy`. Establish `e0 : semi (ν • ofE Δ u) ((0 : Lsq K Δ), y) ∈ S`.

Rewrite using `[← h.stab]`. Conclude with `Set.mem_image_of_mem _ hy`. Establish `e1 : semi (ν • ofE Δ u) ((0 : Lsq K Δ), y) = ((0 : Lsq K Δ), (ν • ofE Δ u) * sigL y)`. Simplify using `[semi]`. Rewrite `e0` using `[e1]`.

Establish `e3` using `hmulv _ e0 (star u) hus.1 hus.2`. Simplify using `only at e3`. Establish `e4` using `hz _ hνs _ e3`. Rewrite `e4` using `[hid]`. Then use the resulting hypothesis. Establish `hsigcmb : ∀ a b : Etau K τ, sigL (cmb Δ s a b) = cmb Δ s a (-b)`.

Introduce `a b`. Apply the tactic sequence `ext <;> simp [sigL, cmb]`. Establish `hw : IsInt O (⟨0, s⟩ : Lsq K Δ)` using `hint _ ⟨0, by simp⟩ ⟨1, by simp⟩`. Establish `hwi : IsInt O (⟨0, s * algebraMap O K ↑ε⁻¹⟩ : Lsq K Δ)` using `hint _ ⟨0, by simp⟩ ⟨↑ε⁻¹, rfl⟩`. Establish `hww : (⟨0, s * algebraMap O K ↑ε⁻¹⟩ : Lsq K Δ) * ⟨0, s⟩ = 1`.

Use `ext`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Take the linear combination `hs`. Simplify using the standard rewrite rules.

Establish `hcmbW : ∀ a b : Etau K τ, cmb Δ s a b = ofE Δ a + (⟨0, s⟩ : Lsq K Δ) • ofE Δ b`. Introduce `a b`. Apply the tactic sequence `ext <;> simp [cmb, ofE]`. Take `⟨t2, ht2⟩` from `L.two`. Establish `hhalf2 : algebraMap O K ↑t2⁻¹ * 2 = 1`.

Use `congrArg (algebraMap O K) (Units.inv_mul t2)` as an intermediate fact. Rewrite `this` using `[map_mul, ht2, map_one, map_ofNat]`. Conclude with `this`. Establish `htwo : (2 : K) ≠ 0`. Introduce `e`.

Rewrite `hhalf2` using `[e, mul_zero]`. Conclude with `zero_ne_one hhalf2`. Establish `hhalf3 : algebraMap O K ↑t2⁻¹ = 2⁻¹` using `eq_inv_of_mul_eq_one_left hhalf2`. Establish `hhalf : IsInt O (algebraMap K (Lsq K Δ) (algebraMap O K ↑t2⁻¹))` using `hint _ ⟨↑t2⁻¹, by simp⟩ ⟨0, by simp⟩`. Establish `hdec : ∀ a b : Etau K τ, ((0 : Lsq K Δ), cmb Δ s a b) ∈ S ↔ ((0 : Lsq K Δ), ofE Δ a) ∈ S ∧ ((0 : Lsq K Δ), ofE Δ b) ∈ S`.

Introduce `a b`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `hA : ((0 : Lsq K Δ), ofE Δ a) ∈ S`. Use `hz _ hhalf _ (hzadd _ _ hy (hsig _ hy))` as an intermediate fact.

Use `this using 2` and compare the differences between its conclusion and the goal. Rewrite using `[hsigcmb, hhalf3]`. Apply the tactic sequence `ext <;> simp [cmb, ofE] <;> field_simp <;> ring`. Use `⟨hA, ?_⟩` and prove the remaining obligations. Establish `e5` using `hz _ hwi _ (hzadd _ _ hy (hz _ hneg1 _ hA))`.

Establish `e6 : cmb Δ s a b + (-1 : Lsq K Δ) • ofE Δ a = (⟨0, s⟩ : Lsq K Δ) • ofE Δ b`. Rewrite using `[hcmbW, neg_one_smul]`. Normalize the expressions using the abelian group laws. Rewrite `e5` using `[e6, smul_smul, hww, one_smul]`. Then use the resulting hypothesis. Introduce and unpack `⟨hA, hB⟩`.

Rewrite using `[hcmbW]`. Conclude with `hzadd _ _ hA (hz _ hw _ hB)`. Establish `hherm : ∀ (x1 : Lsq K Δ) (a b y : Etau K τ), herm c ((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) (x1, cmb Δ s a b) ((0 : Lsq K Δ), ofE Δ y) = ⟨algebraMap O K ↑ε * (t * (τ ^ 2 - 4) * (b * star y).im), s * (t * (τ ^ 2 - 4) * (a * star y).im)⟩`. Introduce `x1 a b y`. Rewrite using `[← cmb_zero s y, herm_cmb]`.

Use `ext`. Simplify using the standard rewrite rules. Conclude with `Or.inl hs`. Simplify using the standard rewrite rules. Establish `hII : ∀ α β : K, IsInt O (⟨algebraMap O K ↑ε * α, s * β⟩ : Lsq K Δ) ↔ α ∈ (algebraMap O K).range ∧ β ∈ (algebraMap O K).range`.

Introduce `α β`. Rewrite using `[(D _).1]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨r, hr⟩, ⟨q, hq⟩⟩`. Use `⟨⟨↑ε⁻¹ * r, ?_⟩, ⟨q, (mul_left_cancel₀ hs0 hq).symm⟩⟩` and prove the remaining obligations.

Establish `hr' : algebraMap O K r = algebraMap O K ↑ε * α` using `hr`. Rewrite using `[map_mul, hr', ← mul_assoc, mul_comm (algebraMap O K ↑ε⁻¹), hεε, one_mul]`. Introduce and unpack `⟨⟨r, hr⟩, ⟨q, hq⟩⟩`. Conclude with `⟨⟨ε * r, by simp [hr]⟩, ⟨q, by simp [hq]⟩⟩`. Establish `hl` using `One.lat O K Δ τ L c _ _ S h 1`.

Simplify using `only [Units.val_one, one_mul] at hl`. Establish `hP : IsFixP O τ (t * (τ ^ 2 - 4)) {a | ((0 : Lsq K Δ), ofE Δ a) ∈ S}`. Use `⟨hl.fg, ?_, ?_⟩` and prove the remaining obligations. Introduce `y show ((0 : Lsq K Δ), ofE Δ y) ∈ S ↔ _`. Rewrite using `[h.dual]`.

Prove the components needed by the constructor for the conclusion. Introduce `H x hx`. Use `H ((0 : Lsq K Δ), ofE Δ x) hx` as an intermediate fact. Rewrite `this` using `[← cmb_zero s x, hherm, hII]`. Conclude with `this.2`.

Introduce `H X hX`. Take `⟨a, b, hab⟩` from `cmb_ex hs0 X.2`. Establish `hX2 : ((0 : Lsq K Δ), X.2) ∈ S` using `((hsplit X).1 hX).2`. Rewrite `hX2` using `[hab, hdec]`. Establish `eX : X = (X.1, cmb Δ s a b)` using `Prod.ext rfl hab`.

Rewrite using `[eX, hherm, hII]`. Conclude with `⟨H b hX2.2, H a hX2.1⟩`. Introduce `x hx`. Use `hmulv _ hx ω ⟨0, by simp⟩ ⟨1, by simp⟩` as an intermediate fact. Simplify using `only at this`.

Rewrite `this` using `[hofE]`. Conclude with `this`. Use `⟨_, hP, ?_⟩` and prove the remaining obligations. Establish `hΦ` using `phi_fix L hg hc hs h1 h2 hτ hu hν hν' hP`. Use extensionality with `x`.

Rewrite using `[hsplit x]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hA, hB⟩`. Establish `hA'` using `One.fst O K Δ τ L hτ hτ' c _ _ hd S _ h hΦ x.1 hA`. Take `⟨a, b, hab⟩` from `cmb_ex hs0 x.2`.

Rewrite `hB` using `[hab, hdec]`. Conclude with `⟨hA'.1, a, hB.1, b, hB.2, hab⟩`. Introduce and unpack `⟨hg', a, ha, b, hb, hab⟩`. Use `⟨One.fst O K Δ τ L hτ hτ' c _ _ hd _ S hΦ h x.1 ⟨hg', 0, fixP_zero hP, 0, fixP_zero hP, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show (0 : EL Δ τ) = cmb Δ s 0 0`.

Apply the tactic sequence `ext <;> simp [cmb]`. Rewrite using `[hab, hdec]`. Conclude with `⟨ha, hb⟩`.
-/
private theorem fix_phi (L : IsLoc O Δ) {c g s t : K} (hg : g ≠ 0) {η ε : Oˣ} (hc : c = algebraMap O K η * g ^ 2)
    (hs : Δ * s ^ 2 = algebraMap O K ε) {u : Etau K τ} (h1 : u.re ∈ (algebraMap O K).range) (h2 : u.im ∈ (algebraMap O K).range)
    (hτ : τ ∈ (algebraMap O K).range) (hτ' : ∃ u : Oˣ, algebraMap O K u = 2 - τ) (hu : QuadraticAlgebra.norm u = 1)
    {ν : Lsq K Δ} (hν : IsInt O ν) (hν' : QuadraticAlgebra.norm ν = -1)
    (hd : IsDat c (ν • ofE Δ u) ((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ))) {S : Set (Sp Δ τ)}
    (h : IsFix O c (ν • ofE Δ u) ((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) S) :
    ∃ S₀, IsFixP O τ (t * (τ ^ 2 - 4)) S₀ ∧ S = Phi O Δ g s S₀ := by
  have hε0 : algebraMap O K ↑ε ≠ 0 := (ε.isUnit.map (algebraMap O K)).ne_zero
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hε0
    rw [← hs]
    ring
  have hεε : algebraMap O K ↑ε * algebraMap O K ↑ε⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have D := descent O K Δ L s ε hs
  have hint : ∀ r : Lsq K Δ, r.re ∈ (algebraMap O K).range →
      (∃ b, r.im = s * algebraMap O K b) → IsInt O r :=
    fun r e1 e2 => ((D r).1).2 ⟨e1, e2⟩
  obtain ⟨hadd, hsm, hfst, hmulv⟩ := One.splitS O K Δ τ L hτ hτ' c _ _ hd S h
  have hofE : ∀ v a : Etau K τ, ofE Δ v * ofE Δ a = ofE Δ (v * a) := by
    intro v a
    have := ofE_cmb (Δ := Δ) 1 v a 0
    rw [cmb_zero, mul_zero, cmb_zero] at this
    exact this
  have hz : ∀ r : Lsq K Δ, IsInt O r → ∀ y : EL Δ τ, ((0 : Lsq K Δ), y) ∈ S →
      ((0 : Lsq K Δ), r • y) ∈ S := by
    intro r hr y hy
    have := hsm _ hy r hr
    simpa using this
  have hzadd : ∀ y y' : EL Δ τ, ((0 : Lsq K Δ), y) ∈ S → ((0 : Lsq K Δ), y') ∈ S →
      ((0 : Lsq K Δ), y + y') ∈ S := by
    intro y y' hy hy'
    have := hadd _ hy _ hy'
    simpa using this
  have hneg1 : IsInt O (-1 : Lsq K Δ) := hint _ ⟨-1, by simp⟩ ⟨0, by simp⟩
  have hsplit : ∀ x : Sp Δ τ, x ∈ S ↔ (x.1, (0 : EL Δ τ)) ∈ S ∧ ((0 : Lsq K Δ), x.2) ∈ S := by
    intro x
    constructor
    · intro hx
      refine ⟨hfst x hx, ?_⟩
      have := hadd _ hx _ (hsm _ (hfst x hx) (-1) hneg1)
      convert this using 1
      exact Prod.ext (by simp) (by simp)
    · rintro ⟨e1, e2⟩
      have := hadd _ e1 _ e2
      convert this using 1
      exact Prod.ext (by simp) (by simp)
  have hus : (star u).re ∈ (algebraMap O K).range ∧ (star u).im ∈ (algebraMap O K).range := by
    obtain ⟨a1, ha1⟩ := h1
    obtain ⟨b1, hb1⟩ := h2
    obtain ⟨t1, ht1⟩ := hτ
    exact ⟨⟨a1 + t1 * b1, by simp [ha1, hb1, ht1]⟩, ⟨-b1, by simp [hb1]⟩⟩
  have hνs : IsInt O (-star ν) := ((D ν).2 hν).neg
  have hid : ∀ w : EL Δ τ, (-star ν) • (ofE Δ (star u) * ((ν • ofE Δ u) * w)) = w := by
    intro w
    have e1 : ofE Δ (star u) * ofE Δ u = 1 := by
      rw [hofE, mul_comm, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hu, map_one]
      ext <;> simp [ofE]
    have e2 : (-star ν) * ν = 1 := by
      rw [neg_mul, mul_comm, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hν']
      simp
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc, e1, one_mul, e2, one_smul]
  have hsig : ∀ y : EL Δ τ, ((0 : Lsq K Δ), y) ∈ S → ((0 : Lsq K Δ), sigL y) ∈ S := by
    intro y hy
    have e0 : semi (ν • ofE Δ u) ((0 : Lsq K Δ), y) ∈ S := by
      rw [← h.stab]
      exact Set.mem_image_of_mem _ hy
    have e1 : semi (ν • ofE Δ u) ((0 : Lsq K Δ), y) = ((0 : Lsq K Δ), (ν • ofE Δ u) * sigL y) := by
      simp [semi]
    rw [e1] at e0
    have e3 := hmulv _ e0 (star u) hus.1 hus.2
    dsimp only at e3
    have e4 := hz _ hνs _ e3
    rwa [hid] at e4
  have hsigcmb : ∀ a b : Etau K τ, sigL (cmb Δ s a b) = cmb Δ s a (-b) := by
    intro a b
    ext <;> simp [sigL, cmb]
  have hw : IsInt O (⟨0, s⟩ : Lsq K Δ) := hint _ ⟨0, by simp⟩ ⟨1, by simp⟩
  have hwi : IsInt O (⟨0, s * algebraMap O K ↑ε⁻¹⟩ : Lsq K Δ) := hint _ ⟨0, by simp⟩ ⟨↑ε⁻¹, rfl⟩
  have hww : (⟨0, s * algebraMap O K ↑ε⁻¹⟩ : Lsq K Δ) * ⟨0, s⟩ = 1 := by
    ext
    · simp
      field_simp
      linear_combination hs
    · simp
  have hcmbW : ∀ a b : Etau K τ, cmb Δ s a b = ofE Δ a + (⟨0, s⟩ : Lsq K Δ) • ofE Δ b := by
    intro a b
    ext <;> simp [cmb, ofE]
  obtain ⟨t2, ht2⟩ := L.two
  have hhalf2 : algebraMap O K ↑t2⁻¹ * 2 = 1 := by
    have := congrArg (algebraMap O K) (Units.inv_mul t2)
    rw [map_mul, ht2, map_one, map_ofNat] at this
    exact this
  have htwo : (2 : K) ≠ 0 := by
    intro e
    rw [e, mul_zero] at hhalf2
    exact zero_ne_one hhalf2
  have hhalf3 : algebraMap O K ↑t2⁻¹ = 2⁻¹ := eq_inv_of_mul_eq_one_left hhalf2
  have hhalf : IsInt O (algebraMap K (Lsq K Δ) (algebraMap O K ↑t2⁻¹)) :=
    hint _ ⟨↑t2⁻¹, by simp⟩ ⟨0, by simp⟩
  have hdec : ∀ a b : Etau K τ, ((0 : Lsq K Δ), cmb Δ s a b) ∈ S ↔
      ((0 : Lsq K Δ), ofE Δ a) ∈ S ∧ ((0 : Lsq K Δ), ofE Δ b) ∈ S := by
    intro a b
    constructor
    · intro hy
      have hA : ((0 : Lsq K Δ), ofE Δ a) ∈ S := by
        have := hz _ hhalf _ (hzadd _ _ hy (hsig _ hy))
        convert this using 2
        rw [hsigcmb, hhalf3]
        ext <;> simp [cmb, ofE] <;> field_simp <;> ring
      refine ⟨hA, ?_⟩
      have e5 := hz _ hwi _ (hzadd _ _ hy (hz _ hneg1 _ hA))
      have e6 : cmb Δ s a b + (-1 : Lsq K Δ) • ofE Δ a = (⟨0, s⟩ : Lsq K Δ) • ofE Δ b := by
        rw [hcmbW, neg_one_smul]
        abel
      rwa [e6, smul_smul, hww, one_smul] at e5
    · rintro ⟨hA, hB⟩
      rw [hcmbW]
      exact hzadd _ _ hA (hz _ hw _ hB)
  have hherm : ∀ (x1 : Lsq K Δ) (a b y : Etau K τ),
      herm c ((t • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) (x1, cmb Δ s a b)
        ((0 : Lsq K Δ), ofE Δ y) =
      ⟨algebraMap O K ↑ε * (t * (τ ^ 2 - 4) * (b * star y).im),
        s * (t * (τ ^ 2 - 4) * (a * star y).im)⟩ := by
    intro x1 a b y
    rw [← cmb_zero s y, herm_cmb]
    ext
    · simp
      exact Or.inl hs
    · simp
  have hII : ∀ α β : K, IsInt O (⟨algebraMap O K ↑ε * α, s * β⟩ : Lsq K Δ) ↔
      α ∈ (algebraMap O K).range ∧ β ∈ (algebraMap O K).range := by
    intro α β
    rw [(D _).1]
    constructor
    · rintro ⟨⟨r, hr⟩, ⟨q, hq⟩⟩
      refine ⟨⟨↑ε⁻¹ * r, ?_⟩, ⟨q, (mul_left_cancel₀ hs0 hq).symm⟩⟩
      have hr' : algebraMap O K r = algebraMap O K ↑ε * α := hr
      rw [map_mul, hr', ← mul_assoc, mul_comm (algebraMap O K ↑ε⁻¹), hεε, one_mul]
    · rintro ⟨⟨r, hr⟩, ⟨q, hq⟩⟩
      exact ⟨⟨ε * r, by simp [hr]⟩, ⟨q, by simp [hq]⟩⟩
  have hl := One.lat O K Δ τ L c _ _ S h 1
  simp only [Units.val_one, one_mul] at hl
  have hP : IsFixP O τ (t * (τ ^ 2 - 4)) {a | ((0 : Lsq K Δ), ofE Δ a) ∈ S} := by
    refine ⟨hl.fg, ?_, ?_⟩
    · intro y
      show ((0 : Lsq K Δ), ofE Δ y) ∈ S ↔ _
      rw [h.dual]
      constructor
      · intro H x hx
        have := H ((0 : Lsq K Δ), ofE Δ x) hx
        rw [← cmb_zero s x, hherm, hII] at this
        exact this.2
      · intro H X hX
        obtain ⟨a, b, hab⟩ := cmb_ex hs0 X.2
        have hX2 : ((0 : Lsq K Δ), X.2) ∈ S := ((hsplit X).1 hX).2
        rw [hab, hdec] at hX2
        have eX : X = (X.1, cmb Δ s a b) := Prod.ext rfl hab
        rw [eX, hherm, hII]
        exact ⟨H b hX2.2, H a hX2.1⟩
    · intro x hx
      have := hmulv _ hx ω ⟨0, by simp⟩ ⟨1, by simp⟩
      dsimp only at this
      rw [hofE] at this
      exact this
  refine ⟨_, hP, ?_⟩
  have hΦ := phi_fix L hg hc hs h1 h2 hτ hu hν hν' hP
  ext x
  rw [hsplit x]
  constructor
  · rintro ⟨hA, hB⟩
    have hA' := One.fst O K Δ τ L hτ hτ' c _ _ hd S _ h hΦ x.1 hA
    obtain ⟨a, b, hab⟩ := cmb_ex hs0 x.2
    rw [hab, hdec] at hB
    exact ⟨hA'.1, a, hB.1, b, hB.2, hab⟩
  · rintro ⟨hg', a, ha, b, hb, hab⟩
    refine ⟨One.fst O K Δ τ L hτ hτ' c _ _ hd _ S hΦ h x.1 ⟨hg', 0, fixP_zero hP, 0, fixP_zero hP, ?_⟩, ?_⟩
    · show (0 : EL Δ τ) = cmb Δ s 0 0
      ext <;> simp [cmb]
    · rw [hab, hdec]
      exact ⟨ha, hb⟩

end

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ L hτ τ₀ hτ₀ hmax c hc u hu2 hu ν hν hν' s ε hs t`. Take `⟨η, g, hg, hcg⟩` from `hc`. Establish `h2 : IsUnit (2 : O)` using `L.two`. Establish `hτr : τ ∈ (algebraMap O K).range` using `⟨τ₀, hτ₀⟩`. Establish `h2τ : ∃ w : Oˣ, algebraMap O K w = 2 - τ`.

Establish `hunit : IsUnit (2 - τ₀)`. Assume the negation of the conclusion as `hn`. Establish `hm : (2 - τ₀) ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 hn`. Establish `h4 : (2 - τ₀) + (τ₀ + 2) ∈ IsLocalRing.maximalIdeal O` using `Ideal.add_mem _ hm hmax`. Establish `e4 : (2 - τ₀) + (τ₀ + 2) = 2 * 2` using `by ring`.

Rewrite `h4` using `[e4]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 h4 (h2.mul h2)`. Take `⟨w, hw⟩` from `hunit`. Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[hw, map_sub, hτ₀, map_ofNat]`.

Take `⟨hur, hui⟩` from `u_int L h2τ hu2 hu`. Establish `hc0 : c ≠ 0`. Rewrite using `[hcg]`. Conclude with `mul_ne_zero (η.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero _ hg)`. Establish `hs0 : Δ * s ^ 2 ≠ 0`.

Rewrite using `[hs]`. Conclude with `(ε.isUnit.map (algebraMap O K)).ne_zero`. Establish `hd` using `isDat_M (c := c) (s := s) (t := (t : K)) hτ hc0 hs0 t.ne_zero hu2 hu hν'`. Establish `hPinv : ∀ (z : (Etau K τ)ˣ) (S : Set (Etau K τ)), IsFixP O τ ((t : K) * (τ ^ 2 - 4)) S → IsFixP O τ ((t : K) * (τ ^ 2 - 4)) ((quo z * ·) '' S)`. Introduce `z S hS`.

Use `PS.fix_ml (PS.qU z) (t := (t : K) * (τ ^ 2 - 4)) (S := S) (by rw [PS.nU_qU, Units.val_one, mul_one]; exact hS)` as an intermediate fact. Simplify `this` using `[PS.ml, PS.qU_val]`. Establish `hFix : ∀ S, IsFix O c (ν • ofE Δ u) (((t : K) • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) S ↔ ∃ S₀, IsFixP O τ ((t : K) * (τ ^ 2 - 4)) S₀ ∧ S = Phi O Δ g s S₀`. Introduce `S`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `fix_phi L hg hcg hs hur hui hτr h2τ hu hν hν' hd h`. Introduce and unpack `⟨S₀, h0, rfl⟩`. Conclude with `phi_fix L hg hcg hs hur hui hτr hu hν hν' h0`. Use `letI := torAct Δ τ`.

Use `letI := quoAct τ`. Unfold `lcount pcount`. Use `wTrans _ _ _ _ _ _ (fun S S₀ => IsFixP O τ ((t : K) * (τ ^ 2 - 4)) S₀ ∧ S = Phi O Δ g s S₀) ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `z S`. Establish `key : ∀ (z : (Etau K τ)ˣ) (S : Set (Sp Δ τ)), IsFix O c (ν • ofE Δ u) (((t : K) • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) S → IsFix O c (ν • ofE Δ u) (((t : K) • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) (z • S)`.

Introduce `z S hS`. Take `⟨S₀, h0, rfl⟩` from `(hFix S).1 hS`. Conclude with `(hFix _).2 ⟨_, hPinv z S₀ h0, phi_act g s S₀ z⟩`. Establish `e : IsFix O c (ν • ofE Δ u) (((t : K) • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) (z • S) ↔ IsFix O c (ν • ofE Δ u) (((t : K) • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) S` using `⟨fun h => by simpa using key z⁻¹ _ h, key z S⟩`. Use `trace_state`.

Rewrite using `[e]`. Introduce `z S`. Establish `e : IsFixP O τ ((t : K) * (τ ^ 2 - 4)) (z • S) ↔ IsFixP O τ ((t : K) * (τ ^ 2 - 4)) S` using `⟨fun h => by`. Establish `h'` using `hPinv z⁻¹ _ h`. Rewrite using `[show ((quo z⁻¹ * ·) '' (z • S)) = z⁻¹ • z • S from rfl, inv_smul_smul] at h', hPinv z S⟩` and apply the resulting hypothesis.

Use `trace_state`. Rewrite using `[e]`. Introduce and unpack `z S S₀ ⟨h0, rfl⟩`. Conclude with `⟨hPinv z S₀ h0, phi_act g s S₀ z⟩`. Introduce and unpack `S S₀ ⟨h0, e⟩`.

Rewrite using `[if_pos ((hFix S).2 ⟨S₀, h0, e⟩), if_pos h0]`. Introduce `S hS`. Establish `hS' : IsFix O c (ν • ofE Δ u) (((t : K) • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) S`. Assume the negation of the conclusion as `hn`. Rewrite `hS` using `[if_neg hn]`.

Conclude with `hS rfl`. Take `⟨S₀, h0, e⟩` from `(hFix S).1 hS'`. Conclude with `⟨S₀, ⟨h0, e⟩, fun S₁ ⟨h1, e1⟩ => phi_inj h1 h0 (e1.symm.trans e)⟩`. Introduce `S₀ hS`. Establish `h0 : IsFixP O τ ((t : K) * (τ ^ 2 - 4)) S₀`.

Assume the negation of the conclusion as `hn`. Rewrite `hS` using `[if_neg hn]`. Conclude with `hS rfl`. Conclude with `⟨Phi O Δ g s S₀, ⟨h0, rfl⟩, fun S ⟨_, e⟩ => e⟩`.
-/
theorem UpperTheory.V.Z.Sym.Loc.caseM :
    UpperTheory.V.Z.Sym.Loc.CaseM := by
  intro O K _ _ _ _ _ Δ τ L hτ τ₀ hτ₀ hmax c hc u hu2 hu ν hν hν' s ε hs t
  obtain ⟨η, g, hg, hcg⟩ := hc
  have h2 : IsUnit (2 : O) := L.two
  have hτr : τ ∈ (algebraMap O K).range := ⟨τ₀, hτ₀⟩
  have h2τ : ∃ w : Oˣ, algebraMap O K w = 2 - τ := by
    have hunit : IsUnit (2 - τ₀) := by
      by_contra hn
      have hm : (2 - τ₀) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hn
      have h4 : (2 - τ₀) + (τ₀ + 2) ∈ IsLocalRing.maximalIdeal O := Ideal.add_mem _ hm hmax
      have e4 : (2 - τ₀) + (τ₀ + 2) = 2 * 2 := by ring
      rw [e4] at h4
      exact (IsLocalRing.mem_maximalIdeal _).1 h4 (h2.mul h2)
    obtain ⟨w, hw⟩ := hunit
    refine ⟨w, ?_⟩
    rw [hw, map_sub, hτ₀, map_ofNat]
  obtain ⟨hur, hui⟩ := u_int L h2τ hu2 hu
  have hc0 : c ≠ 0 := by
    rw [hcg]
    exact mul_ne_zero (η.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero _ hg)
  have hs0 : Δ * s ^ 2 ≠ 0 := by
    rw [hs]
    exact (ε.isUnit.map (algebraMap O K)).ne_zero
  have hd := isDat_M (c := c) (s := s) (t := (t : K)) hτ hc0 hs0 t.ne_zero hu2 hu hν'
  have hPinv : ∀ (z : (Etau K τ)ˣ) (S : Set (Etau K τ)), IsFixP O τ ((t : K) * (τ ^ 2 - 4)) S →
      IsFixP O τ ((t : K) * (τ ^ 2 - 4)) ((quo z * ·) '' S) := by
    intro z S hS
    have := PS.fix_ml (PS.qU z) (t := (t : K) * (τ ^ 2 - 4)) (S := S)
      (by rw [PS.nU_qU, Units.val_one, mul_one]; exact hS)
    simpa [PS.ml, PS.qU_val] using this
  have hFix : ∀ S, IsFix O c (ν • ofE Δ u) (((t : K) • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) S ↔
      ∃ S₀, IsFixP O τ ((t : K) * (τ ^ 2 - 4)) S₀ ∧ S = Phi O Δ g s S₀ := by
    intro S
    constructor
    · intro h
      exact fix_phi L hg hcg hs hur hui hτr h2τ hu hν hν' hd h
    · rintro ⟨S₀, h0, rfl⟩
      exact phi_fix L hg hcg hs hur hui hτr hu hν hν' h0
  letI := torAct Δ τ
  letI := quoAct τ
  unfold lcount pcount
  refine wTrans _ _ _ _ _ _ (fun S S₀ => IsFixP O τ ((t : K) * (τ ^ 2 - 4)) S₀ ∧ S = Phi O Δ g s S₀)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro z S
    have key : ∀ (z : (Etau K τ)ˣ) (S : Set (Sp Δ τ)),
        IsFix O c (ν • ofE Δ u) (((t : K) • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) S →
        IsFix O c (ν • ofE Δ u) (((t : K) • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) (z • S) := by
      intro z S hS
      obtain ⟨S₀, h0, rfl⟩ := (hFix S).1 hS
      exact (hFix _).2 ⟨_, hPinv z S₀ h0, phi_act g s S₀ z⟩
    have e : IsFix O c (ν • ofE Δ u) (((t : K) • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) (z • S) ↔
        IsFix O c (ν • ofE Δ u) (((t : K) • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) S :=
      ⟨fun h => by simpa using key z⁻¹ _ h, key z S⟩
    trace_state
    rw [e]
  · intro z S
    have e : IsFixP O τ ((t : K) * (τ ^ 2 - 4)) (z • S) ↔ IsFixP O τ ((t : K) * (τ ^ 2 - 4)) S :=
      ⟨fun h => by
        have h' := hPinv z⁻¹ _ h
        rwa [show ((quo z⁻¹ * ·) '' (z • S)) = z⁻¹ • z • S from rfl, inv_smul_smul] at h', hPinv z S⟩
    trace_state
    rw [e]
  · rintro z S S₀ ⟨h0, rfl⟩
    exact ⟨hPinv z S₀ h0, phi_act g s S₀ z⟩
  · rintro S S₀ ⟨h0, e⟩
    rw [if_pos ((hFix S).2 ⟨S₀, h0, e⟩), if_pos h0]
  · intro S hS
    have hS' : IsFix O c (ν • ofE Δ u) (((t : K) • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) S := by
      by_contra hn
      rw [if_neg hn] at hS
      exact hS rfl
    obtain ⟨S₀, h0, e⟩ := (hFix S).1 hS'
    exact ⟨S₀, ⟨h0, e⟩, fun S₁ ⟨h1, e1⟩ => phi_inj h1 h0 (e1.symm.trans e)⟩
  · intro S₀ hS
    have h0 : IsFixP O τ ((t : K) * (τ ^ 2 - 4)) S₀ := by
      by_contra hn
      rw [if_neg hn] at hS
      exact hS rfl
    exact ⟨Phi O Δ g s S₀, ⟨h0, rfl⟩, fun S ⟨_, e⟩ => e⟩
