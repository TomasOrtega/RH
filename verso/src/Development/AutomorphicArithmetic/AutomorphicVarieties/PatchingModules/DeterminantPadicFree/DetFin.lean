import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PhiSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.AcConst
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SubMulAddEpM
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FinSub

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `N`. Simplify `(hf N).comp₂ (hh N) (· * ·)` using `only [map_mul]`.
-/
private theorem ac_mul {G R : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} {f h : G → R}
    (hf : AdicCont I f) (hh : AdicCont I h) : AdicCont I fun g => f g * h g := by
  intro N
  simpa only [map_mul] using (hf N).comp₂ (hh N) (· * ·)

/- English proof (translation)
Introduce `N`. Simplify `(hf N).comp₂ (hh N) (· + ·)` using `only [map_add]`.
-/
private theorem ac_add {G R : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} {f h : G → R}
    (hf : AdicCont I f) (hh : AdicCont I h) : AdicCont I fun g => f g + h g := by
  intro N
  simpa only [map_add] using (hf N).comp₂ (hh N) (· + ·)

/- English proof (translation)
Introduce `_` and use `IsLocallyConstant.const _`.
-/
private theorem ac_const {G R : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} (c : R) :
    AdicCont I fun _ : G => c := fun _ => IsLocallyConstant.const _

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using ac_const (G := G) (I := I) 0`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`. Conclude with `ac_add (hf a) ih`.
-/
private theorem ac_sum {G R ι : Type} [TopologicalSpace G] [CommRing R] {I : Ideal R} (s : Finset ι)
    {f : ι → G → R} (hf : ∀ i, AdicCont I (f i)) : AdicCont I fun g => ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ac_const (G := G) (I := I) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ac_add (hf a) ih

/- English proof (translation)
Introduce `N`. Establish `hle : (Ideal.span {t}) ^ N ≤ ((Ideal.span {φ t}) ^ N).comap φ`. Rewrite using `[← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span, Set.image_singleton]`. Establish `h` using `(hf N).comp (Ideal.quotientMap ((Ideal.span {φ t}) ^ N) φ hle)`. Simplify `h` using `[Function.comp_def, Ideal.quotientMap_mk]`.
-/
private theorem ac_map {G A R : Type} [TopologicalSpace G] [CommRing A] [CommRing R] (φ : A →+* R) (t : A)
    {f : G → A} (hf : AdicCont (Ideal.span {t}) f) : AdicCont (Ideal.span {φ t}) fun g => φ (f g) := by
  intro N
  have hle : (Ideal.span {t}) ^ N ≤ ((Ideal.span {φ t}) ^ N).comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span, Set.image_singleton]
  have h := (hf N).comp (Ideal.quotientMap ((Ideal.span {φ t}) ^ N) φ hle)
  simpa [Function.comp_def, Ideal.quotientMap_mk] using h

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `using h0`. Introduce `i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, ha, ih]`.
-/
private theorem dd_sum {X ι Y : Type} [CommRing X] [AddCommMonoid Y] {g : ℕ} (p : DD X g → Y) (h0 : p 0 = 0)
    (ha : ∀ x y, p (x + y) = p x + p y) (s : Finset ι) (f : ι → DD X g) : p (∑ i ∈ s, f i) = ∑ i ∈ s, p (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using h0
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ha, ih]

/- English proof (translation)
Establish `hm : ∀ j, DD.C (Z j a b) * (⟨0, Pi.single j 1, 0, 0⟩ : DD X g) = (⟨0, Pi.single j (Z j a b), 0, 0⟩ : DD X g)`. Introduce `j`. Apply `DD.ext` to reduce the goal to its premises. Use `show Z j a b * 0 = 0`. Simplify using the standard rewrite rules.

Use function extensionality and compare the values at `i show Z j a b * (Pi.single j (1 : X) : Fin g → X) i + (0 : Fin g → X) i * 0 = (Pi.single j (Z j a b) : Fin g → X) i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`.

Use function extensionality and compare the values at `i show Z j a b * (0 : Fin g → X) i + (0 : Fin g → X) i * 0 = (0 : Fin g → X) i`. Simplify using the standard rewrite rules. Use `show Z j a b * 0 + 0 * 0 + ∑ k, ((0 : Fin g → X) k * (0 : Fin g → X) k + (0 : Fin g → X) k * (Pi.single j (1 : X) : Fin g → X) k) = 0`. Simplify using the standard rewrite rules. Repeatedly rewrite using `[hm]`.

Use extensionality with `i`. Rewrite using `[dd_sum (fun x : DD X g => x.a) rfl (fun _ _ => rfl)]`. Simplify using `[DD.epM]`. Rewrite using `[dd_sum (fun x : DD X g => x.ep i) rfl (fun _ _ => rfl)]`. Simplify using `[DD.epM, Pi.single_apply]`.

Rewrite using `[dd_sum (fun x : DD X g => x.ep' i) rfl (fun _ _ => rfl)]`. Simplify using `[DD.epM]`. Rewrite using `[dd_sum (fun x : DD X g => x.eta) rfl (fun _ _ => rfl)]`. Simplify using `[DD.epM]`.
-/
private theorem epM_entry {X : Type} [CommRing X] {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) X) (a b : Fin n) :
    DD.epM Z a b = ∑ j, DD.C (Z j a b) * (⟨0, Pi.single j 1, 0, 0⟩ : DD X g) := by
  have hm : ∀ j, DD.C (Z j a b) * (⟨0, Pi.single j 1, 0, 0⟩ : DD X g)
      = (⟨0, Pi.single j (Z j a b), 0, 0⟩ : DD X g) := by
    intro j
    apply DD.ext
    · show Z j a b * 0 = 0
      simp
    · funext i
      show Z j a b * (Pi.single j (1 : X) : Fin g → X) i + (0 : Fin g → X) i * 0
        = (Pi.single j (Z j a b) : Fin g → X) i
      by_cases h : i = j
      · subst h
        simp
      · simp [Pi.single_apply, h]
    · funext i
      show Z j a b * (0 : Fin g → X) i + (0 : Fin g → X) i * 0 = (0 : Fin g → X) i
      simp
    · show Z j a b * 0 + 0 * 0 + ∑ k, ((0 : Fin g → X) k * (0 : Fin g → X) k
          + (0 : Fin g → X) k * (Pi.single j (1 : X) : Fin g → X) k) = 0
      simp
  simp_rw [hm]
  ext i
  · rw [dd_sum (fun x : DD X g => x.a) rfl (fun _ _ => rfl)]
    simp [DD.epM]
  · rw [dd_sum (fun x : DD X g => x.ep i) rfl (fun _ _ => rfl)]
    simp [DD.epM, Pi.single_apply]
  · rw [dd_sum (fun x : DD X g => x.ep' i) rfl (fun _ _ => rfl)]
    simp [DD.epM]
  · rw [dd_sum (fun x : DD X g => x.eta) rfl (fun _ _ => rfl)]
    simp [DD.epM]

private noncomputable def ddLin (A : Type) [CommRing A] (g : ℕ) :
    DD A g ≃ₗ[A] A × (Fin g → A) × (Fin g → A) × A :=
  { DD.equiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun c x => by
      have hc : c • x = DD.C c * x := rfl
      rw [hc]
      ext <;> simp [DD.equiv] }

/- English proof (translation)
Establish `hl : (algebraMap ℤ_[l] K) (l : ℤ_[l]) = 0`. Assume the negation of the conclusion as `hne`. Establish `hinj : Function.Injective (algebraMap ℤ_[l] K)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`.

Assume the negation of the conclusion as `ha0`. Establish `hker : RingHom.ker (algebraMap ℤ_[l] K) ≠ ⊥`. Introduce `h`. Apply `ha0` to reduce the goal to its premises. Establish `hmem : a ∈ RingHom.ker (algebraMap ℤ_[l] K)` using `ha`.

Rewrite `hmem` using `[h]`. Conclude with `hmem`. Take `⟨m, hm⟩` from `PadicInt.ideal_eq_span_pow_p hker`. Establish `hmem : (l : ℤ_[l]) ^ m ∈ RingHom.ker (algebraMap ℤ_[l] K)`. Rewrite using `[hm]`.

Conclude with `Ideal.subset_span rfl`. Rewrite `hmem` using `[RingHom.mem_ker, map_pow]`. Conclude with `hne (pow_eq_zero_iff'.mp hmem).1`. Establish `: Finite ℤ_[l]` using `Finite.of_injective _ hinj`. Establish `: Finite ℤ` using `Finite.of_injective (Int.cast : ℤ → ℤ_[l]) Int.cast_injective`.

Conclude with `not_finite ℤ`. Establish `hK : ((l : ℕ) : K) = 0`. Rewrite using `[← map_natCast (algebraMap ℤ_[l] K)]`. Conclude with `hl`. Conclude with `(CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).mpr hK`.
-/
private theorem charK (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] : CharP K l := by
  have hl : (algebraMap ℤ_[l] K) (l : ℤ_[l]) = 0 := by
    by_contra hne
    have hinj : Function.Injective (algebraMap ℤ_[l] K) := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra ha0
      have hker : RingHom.ker (algebraMap ℤ_[l] K) ≠ ⊥ := by
        intro h
        apply ha0
        have hmem : a ∈ RingHom.ker (algebraMap ℤ_[l] K) := ha
        rw [h] at hmem
        exact hmem
      obtain ⟨m, hm⟩ := PadicInt.ideal_eq_span_pow_p hker
      have hmem : (l : ℤ_[l]) ^ m ∈ RingHom.ker (algebraMap ℤ_[l] K) := by
        rw [hm]
        exact Ideal.subset_span rfl
      rw [RingHom.mem_ker, map_pow] at hmem
      exact hne (pow_eq_zero_iff'.mp hmem).1
    have : Finite ℤ_[l] := Finite.of_injective _ hinj
    have : Finite ℤ := Finite.of_injective (Int.cast : ℤ → ℤ_[l]) Int.cast_injective
    exact not_finite ℤ
  have hK : ((l : ℕ) : K) = 0 := by
    rw [← map_natCast (algebraMap ℤ_[l] K)]
    exact hl
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).mpr hK

/- English proof (translation)
Establish `hφ : IsLocallyConstant (φ : ℤ_[l] → R)`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Use `filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy`. Rewrite `hy` using `[Metric.mem_ball, dist_eq_norm, PadicInt.norm_lt_one_iff_dvd]`.

Take `⟨c, hc⟩` from `hy`. Establish `hy' : y = x + (l : ℤ_[l]) * c` using `by rw [← hc]; ring`. Rewrite using `[hy', map_add, map_mul, map_natCast, hl, zero_mul, add_zero]`. Conclude with `hφ.comp_continuous he`.
-/
private theorem lc_zp {l : ℕ} [Fact l.Prime] {G R : Type} [TopologicalSpace G] [CommRing R] (φ : ℤ_[l] →+* R)
    (hl : (l : R) = 0) {e : G → ℤ_[l]} (he : Continuous e) : IsLocallyConstant fun g => φ (e g) := by
  have hφ : IsLocallyConstant (φ : ℤ_[l] → R) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
    rw [Metric.mem_ball, dist_eq_norm, PadicInt.norm_lt_one_iff_dvd] at hy
    obtain ⟨c, hc⟩ := hy
    have hy' : y = x + (l : ℤ_[l]) * c := by rw [← hc]; ring
    rw [hy', map_add, map_mul, map_natCast, hl, zero_mul, add_zero]
  exact hφ.comp_continuous he

/- English proof (translation)
Introduce `l _ F n x k S hΦ hdet`. Use `haveI : CharP x.K l := charK l x.K`. Use `haveI : Module.Free x.A (DD x.A k.g) := Module.Free.of_equiv (ddLin x.A k.g).symm`. Use `haveI : Module.Finite x.A (DD x.A k.g) := Module.Finite.equiv (ddLin x.A k.g).symm`. Use `haveI : CompactSpace F.G₀ := isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact`.

Set `I : Ideal (DD x.A k.g)` to `Ideal.span {algebraMap x.A (DD x.A k.g) x.t}`. Set `χ : F.G₀ →* DD x.A k.g` to `(algebraMap x.A (DD x.A k.g)).toMonoidHom.comp ((algebraMap ℤ_[l] x.A).toMonoidHom.comp ((Units.coeHom ℤ_[l]).comp (F.ε.comp F.η.ker.subtype)))`. Set `r : F.G₀ →* Matrix (Fin n) (Fin n) (DD x.A k.g)` to `⟨⟨k.ρ1 x.A, (Det.rho1Hom k x.A).1⟩, (Det.rho1Hom k x.A).2.1⟩`. Set `Zb : Submodule x.A (F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g))` to `{ carrier := {z | (∀ i j, AdicCont I fun g => z g i j) ∧ TwCoc (⇑χ) (⇑r) Set.univ z} zero_mem' := by`. Use `⟨fun _ _ => ac_const 0, fun g _ h _ => ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Use the proof step `add_mem' := by`. Introduce `a b ha hb`. Use `⟨fun i j => ac_add (ha.1 i j) (hb.1 i j), fun g _ h _ => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`.

Rewrite using `[ha.2 g trivial h trivial, hb.2 g trivial h trivial]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, smul_add]`. Normalize the expressions using the abelian group laws. Use the proof step `smul_mem' := by`. Introduce `c z hz`.

Use `⟨fun i j => ?_, fun g _ h _ => ?_⟩` and prove the remaining obligations. Establish `h` using `ac_mul (ac_const (G := F.G₀) (I := I) (algebraMap x.A (DD x.A k.g) c)) (hz.1 i j)`. Simplify `h` using `[Algebra.smul_def]`. Simplify using `only [Pi.smul_apply]`. Rewrite using `[hz.2 g trivial h trivial, smul_add, Matrix.mul_smul, Matrix.smul_mul, smul_comm c (χ g)] }`.

Establish `hG : PhiCond F.G₀ l` using `Det.phiSub l F.η.ker F.η_open hΦ`. Establish `he : Continuous fun g : F.G₀ => ((F.ε g : ℤ_[l]ˣ) : ℤ_[l])` using `Units.continuous_val.comp (F.ε_cont.comp continuous_subtype_val)`. Establish `hA : AdicCont (Ideal.span {x.t}) fun g : F.G₀ => algebraMap ℤ_[l] x.A (F.ε g)`. Introduce `N`. Establish `hl : ((l : ℕ) : x.A ⧸ (Ideal.span {x.t}) ^ N) = 0`.

Rewrite using `[← map_natCast (Ideal.Quotient.mk _), ← map_natCast (algebraMap x.K x.A), CharP.cast_eq_zero, map_zero, map_zero]`. Conclude with `lc_zp ((Ideal.Quotient.mk _).comp (algebraMap ℤ_[l] x.A)) hl he`. Establish `hχ : AdicCont I χ` using `ac_map (algebraMap x.A (DD x.A k.g)) x.t hA`. Establish `hE : ∀ a b, AdicCont I fun g => DD.epM (fun j => (k.κ j g).map (algebraMap x.A x.A)) a b`. Introduce `a b`.

Repeatedly rewrite using `[epM_entry]`. Use `ac_sum _ (fun j => ac_mul ?_ (ac_const _))` and prove the remaining obligations. Conclude with `ac_map (algebraMap x.A (DD x.A k.g)) x.t ((k.mem j).2.1 a b)`. Establish `hρ : ∀ a b, AdicCont I fun g => x.ρX (DD x.A k.g) g a b`. Introduce `a b`.

Establish `h` using `x.cont a b`. Rewrite `h` using `[PowerSeries.maximalIdeal_eq_span_X]`. Conclude with `ac_map (algebraMap x.A (DD x.A k.g)) PowerSeries.X h`. Establish `hr : ∀ i j, AdicCont I fun g => r g i j`. Introduce `i j`.

Use `show AdicCont I fun g => ((1 + DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A)) * x.ρX (DD x.A k.g) g) i j`. Simplify using `only [Matrix.mul_apply, Matrix.add_apply]`. Conclude with `ac_sum _ fun m => ac_mul (ac_add (ac_const _) (hE i m)) (hρ m j)`. Establish `hFG : Zb.FG` using `Det.matFg l χ r Zb hG hχ hr (fun z hz => hz)`. Set `etaL : DD x.A k.g →ₗ[x.A] x.A` to `(LinearMap.snd x.A _ _).comp ((LinearMap.snd x.A _ _).comp ((LinearMap.snd x.A _ _).comp (ddLin x.A k.g).toLinearMap))`.

Set `f : S → (F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)) →ₗ[x.A] x.A` to `fun σ => etaL.comp ((Matrix.traceLinearMap (Fin n) x.A (DD x.A k.g)).comp ((LinearMap.mulRight x.A (k.ρ1 x.A σ)).comp (LinearMap.proj (σ : F.G₀))))`. Set `B : Submodule x.A (F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g))` to `⨅ σ : S, LinearMap.ker (f σ)`. Take `⟨T, hT⟩` from `Det.finSub x.t Zb B f PowerSeries.X_irreducible hFG (fun i b hb => LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hb i)) (fun z _ hz => ⟨0, by`. Rewrite using `[pow_zero, one_smul]`. Conclude with `(Submodule.mem_iInf _).mpr fun i => LinearMap.mem_ker.mpr (hz i)⟩)`.

Use `⟨T.map (Function.Embedding.subtype _), ?_, ?_⟩` and prove the remaining obligations. Introduce `σ hσ`. Rewrite `hσ` using `[Finset.coe_map, Set.mem_image]`. Take `⟨i, _, rfl⟩` from `hσ`. Conclude with `i.2`.

Introduce `z hz hvan`. Establish `hzZ : z ∈ Zb` using `⟨hz.2.1, fun g _ h _ => hz.2.2.1 g h⟩`. Take `⟨s, hs⟩` from `hT z hzZ (fun i hi => hvan _ (Finset.mem_map_of_mem _ hi))`. Apply `hdet z hz` to reduce the goal to its premises. Introduce `σ hσ`.

Establish `h1 : f ⟨σ, hσ⟩ (x.t ^ s • z) = 0` using `LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hs ⟨σ, hσ⟩)`. Rewrite `h1` using `[map_smul, smul_eq_mul]`. Conclude with `(mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)`.
-/
theorem UpperTheory.V.Pa.Det.detFin :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (S : Set F.G₀), PhiCond F.Γ l → Detects k S → ∃ T : Finset F.G₀, (T : Set F.G₀) ⊆ S ∧ Detects k (T : Set F.G₀) := by
  intro l _ F n x k S hΦ hdet
  classical
  haveI : CharP x.K l := charK l x.K
  haveI : Module.Free x.A (DD x.A k.g) := Module.Free.of_equiv (ddLin x.A k.g).symm
  haveI : Module.Finite x.A (DD x.A k.g) := Module.Finite.equiv (ddLin x.A k.g).symm
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  let I : Ideal (DD x.A k.g) := Ideal.span {algebraMap x.A (DD x.A k.g) x.t}
  let χ : F.G₀ →* DD x.A k.g :=
    (algebraMap x.A (DD x.A k.g)).toMonoidHom.comp ((algebraMap ℤ_[l] x.A).toMonoidHom.comp
      ((Units.coeHom ℤ_[l]).comp (F.ε.comp F.η.ker.subtype)))
  let r : F.G₀ →* Matrix (Fin n) (Fin n) (DD x.A k.g) :=
    ⟨⟨k.ρ1 x.A, (Det.rho1Hom k x.A).1⟩, (Det.rho1Hom k x.A).2.1⟩
  let Zb : Submodule x.A (F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)) :=
    { carrier := {z | (∀ i j, AdicCont I fun g => z g i j) ∧ TwCoc (⇑χ) (⇑r) Set.univ z}
      zero_mem' := by
        refine ⟨fun _ _ => ac_const 0, fun g _ h _ => ?_⟩
        simp
      add_mem' := by
        intro a b ha hb
        refine ⟨fun i j => ac_add (ha.1 i j) (hb.1 i j), fun g _ h _ => ?_⟩
        simp only [Pi.add_apply]
        rw [ha.2 g trivial h trivial, hb.2 g trivial h trivial]
        simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
        abel
      smul_mem' := by
        intro c z hz
        refine ⟨fun i j => ?_, fun g _ h _ => ?_⟩
        · have h := ac_mul (ac_const (G := F.G₀) (I := I) (algebraMap x.A (DD x.A k.g) c)) (hz.1 i j)
          simpa [Algebra.smul_def] using h
        · simp only [Pi.smul_apply]
          rw [hz.2 g trivial h trivial, smul_add, Matrix.mul_smul, Matrix.smul_mul, smul_comm c (χ g)] }
  have hG : PhiCond F.G₀ l := Det.phiSub l F.η.ker F.η_open hΦ
  have he : Continuous fun g : F.G₀ => ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (F.ε_cont.comp continuous_subtype_val)
  have hA : AdicCont (Ideal.span {x.t}) fun g : F.G₀ => algebraMap ℤ_[l] x.A (F.ε g) := by
    intro N
    have hl : ((l : ℕ) : x.A ⧸ (Ideal.span {x.t}) ^ N) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), ← map_natCast (algebraMap x.K x.A),
        CharP.cast_eq_zero, map_zero, map_zero]
    exact lc_zp ((Ideal.Quotient.mk _).comp (algebraMap ℤ_[l] x.A)) hl he
  have hχ : AdicCont I χ := ac_map (algebraMap x.A (DD x.A k.g)) x.t hA
  have hE : ∀ a b, AdicCont I fun g => DD.epM (fun j => (k.κ j g).map (algebraMap x.A x.A)) a b := by
    intro a b
    simp_rw [epM_entry]
    refine ac_sum _ (fun j => ac_mul ?_ (ac_const _))
    exact ac_map (algebraMap x.A (DD x.A k.g)) x.t ((k.mem j).2.1 a b)
  have hρ : ∀ a b, AdicCont I fun g => x.ρX (DD x.A k.g) g a b := by
    intro a b
    have h := x.cont a b
    rw [PowerSeries.maximalIdeal_eq_span_X] at h
    exact ac_map (algebraMap x.A (DD x.A k.g)) PowerSeries.X h
  have hr : ∀ i j, AdicCont I fun g => r g i j := by
    intro i j
    show AdicCont I fun g => ((1 + DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A))
      * x.ρX (DD x.A k.g) g) i j
    simp only [Matrix.mul_apply, Matrix.add_apply]
    exact ac_sum _ fun m => ac_mul (ac_add (ac_const _) (hE i m)) (hρ m j)
  have hFG : Zb.FG := Det.matFg l χ r Zb hG hχ hr (fun z hz => hz)
  let etaL : DD x.A k.g →ₗ[x.A] x.A :=
    (LinearMap.snd x.A _ _).comp ((LinearMap.snd x.A _ _).comp
      ((LinearMap.snd x.A _ _).comp (ddLin x.A k.g).toLinearMap))
  let f : S → (F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)) →ₗ[x.A] x.A := fun σ =>
    etaL.comp ((Matrix.traceLinearMap (Fin n) x.A (DD x.A k.g)).comp
      ((LinearMap.mulRight x.A (k.ρ1 x.A σ)).comp (LinearMap.proj (σ : F.G₀))))
  let B : Submodule x.A (F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)) := ⨅ σ : S, LinearMap.ker (f σ)
  obtain ⟨T, hT⟩ := Det.finSub x.t Zb B f PowerSeries.X_irreducible hFG
    (fun i b hb => LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hb i))
    (fun z _ hz => ⟨0, by
      rw [pow_zero, one_smul]
      exact (Submodule.mem_iInf _).mpr fun i => LinearMap.mem_ker.mpr (hz i)⟩)
  refine ⟨T.map (Function.Embedding.subtype _), ?_, ?_⟩
  · intro σ hσ
    rw [Finset.coe_map, Set.mem_image] at hσ
    obtain ⟨i, _, rfl⟩ := hσ
    exact i.2
  · intro z hz hvan
    have hzZ : z ∈ Zb := ⟨hz.2.1, fun g _ h _ => hz.2.2.1 g h⟩
    obtain ⟨s, hs⟩ := hT z hzZ (fun i hi => hvan _ (Finset.mem_map_of_mem _ hi))
    apply hdet z hz
    intro σ hσ
    have h1 : f ⟨σ, hσ⟩ (x.t ^ s • z) = 0 :=
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hs ⟨σ, hσ⟩)
    rw [map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)
