import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NormInj
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ExtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

/- English proof (translation)
Unfold `quotIntegral`. Use `split_ifs`. Simplify using `only [mul_assoc, integral_const_mul]`. Simplify using the standard rewrite rules.
-/
private theorem quot_smul {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (H : Subgroup G) (ν : Measure H) (c : ℂ) (F : G → ℂ) :
    quotIntegral μ H ν (fun g => c * F g) = c * quotIntegral μ H ν F := by
  unfold quotIntegral
  split_ifs
  · simp only [mul_assoc, integral_const_mul]
  · simp

/- English proof (translation)
Use `quot_smul μ H ν 0 F` as an intermediate fact. Rewrite `this` using `[zero_mul]`. Rewrite using `[← this]`. Use `congr 1`. Use function extensionality and compare the values at `g`.

Rewrite using `[h, mul_zero]`.
-/
private theorem quot_zero {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (H : Subgroup G) (ν : Measure H) (F : G → ℂ)
    (h : ∀ g, F g = 0) : quotIntegral μ H ν F = 0 := by
  have := quot_smul μ H ν 0 F
  rw [zero_mul] at this
  rw [← this]
  congr 1
  funext g
  rw [h, mul_zero]

/- English proof (translation)
Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_div, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
private theorem alg {A : Type} [CommGroup A] (d a b u v t : A) : d * a / u / t = d * b / v / t * (b⁻¹ * a / (v⁻¹ * u)) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Introduce `k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ n _ _ _ _ μE μk hE hk r hr0 hr1`. Take `⟨r₀, h00, h01, hn⟩` from `hN k E σ hσ r hr0 hr1`. Use `⟨r₀, h00, h01, fun r' hle h'0 => ⟨fun x hx => (hn x (hx.trans hle)).2, ?_⟩⟩` and prove the remaining obligations. Establish `h'1 : r' < 1` using `hle.trans_lt h01`. Take `⟨hcyc, -, hbr⟩` from `bridge k E σ`.

Take `⟨hsg, -, -, hcl, -⟩` from `hbr n`. Establish `hc1 : Cyc (RingEquiv.refl k) 1` using `⟨fun _ => rfl, one_pos, fun _ => rfl⟩`. Take `⟨R, hRne, hR1, hR2, hnear, hR3⟩` from `hR E n σ _ hcyc r hr0 hr1`. Take `⟨j, hj, hvol⟩` from `hV k E σ hσ n r r' hr0 hr1 h'0 h'1 fun x hx => (hn x (hx.trans hle)).1`. Take `⟨d1, d2, d3⟩` from `hD k E σ hσ n`.

Take `⟨K, hK, hKo, hKc⟩` from `hB E n r hr0 hr1`. Take `⟨K', hK', hKo', hKc'⟩` from `hB k n r' h'0 h'1`. Take `⟨a1, a2, a3, -⟩` from `UpperTheory.V.Z.Tf.Orb.gLTop E n`. Establish `pE : 0 < μE.real (ball n r)` using `hK ▸ ENNReal.toReal_pos (hKo.measure_ne_zero μE ⟨1, one_mem _⟩) hKc.measure_ne_top`. Establish `pk : 0 < μk.real (ball n r')` using `hK' ▸ ENNReal.toReal_pos (hKo'.measure_ne_zero μk ⟨1, one_mem _⟩) hKc'.measure_ne_top`.

Establish `pR : (0 : ℝ) < R.card` using `Nat.cast_pos.2 hRne.card_pos`. Use `⟨R.card * μE.real (ball n r) / (j * μk.real (ball n r')), by positivity, fun t ht => ?_⟩` and prove the remaining obligations. Establish `hA1 : ∀ x ∈ ({t} : Set (Fin n → Eˣ)), Strict x` using `fun x hx => hx ▸ ht`. Establish `hA2` using `(d3 r hr1 t ht).1`. Establish `key : ∀ x ∈ nrmSet k r t, ∀ s, Near r' s → x * s ∈ nrmSet k r t`.

Introduce and unpack `_ ⟨u, hu, rfl⟩ s hs`. Use `choose u' hu' hu'' using fun i => (hn (s i) ((hs i).trans hle)).2`. Use `⟨u * u', (hnear u u' hu hu').1, funext fun i => Units.ext ?_⟩` and prove the remaining obligations. Simplify using `only [nrmT, Pi.mul_apply, Units.val_mul, Units.coe_map, map_mul, hu'', mul_assoc]`. Take `⟨-, -, -, -, hnear', -⟩` from `hR k n _ _ hc1 r' h'0 h'1`.

Establish `meet' : ∀ γ g : GL (Fin n) k, g⁻¹ * γ * g ∈ elemSet r' (nrmSet k r t) → ∃ d : Fin n → Eˣ, Strict d ∧ IsNormOf σ (diagT E (Fin n) d) γ` using `fun γ g hg => by`. Take `⟨y, x, hx, s, hs, -, e⟩` from `(hS k n _ _ hc1 r' h'0 h'1 _ hA2).1 γ g hg`. Take `⟨u, hu, e'⟩` from `key x hx s hs`. Use `⟨t * u, fun i i' h => ?_, (incl y)⁻¹, ?_⟩` and prove the remaining obligations. Establish `hv : ∀ i, valuation E (u i : E) = 1` using `fun i => by`.

Use `Valuation.map_one_add_of_lt (valuation E) ((hu i).trans_lt hr1)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Simplify `ht i i' h` using `[hv]`. Rewrite using `[(d1 _).1, ← e', ← e, inv_inv, map_mul, map_mul, map_inv]`. Both sides reduce to the same expression.

Use `⟨fun δ γ h μδ μγ hδ hNm hμδ hμγ hm => ?_, fun γ μγ hγ hnn hμ => ?_⟩` and prove the remaining obligations. Unfold `twOrbIntegralC orbIntegralC`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[quot_smul]`. Distinguish the cases in `hcase : ∃ y d, Strict d ∧ y⁻¹ * δ * sigmaGL σ y = diagT E (Fin n) d`.

Take `⟨y, d, hd, hy⟩` from `hcase`. Take `⟨y', hy', hal⟩` from `hA k E σ hσ n δ h y γ d hd hNm hy`. Establish `oE` using `hO E n σ _ hcyc r hr0 hr1 μE hE _ hA1 δ y d hd (by rw [hsg]; exact hy) (twCent (sigmaGL σ) δ) (fun c => by rw [hsg]; rfl) μδ hμδ`. Establish `ok` using `hO k n _ _ hc1 r' h'0 h'1 μk hk _ hA2 γ y' (nrmT k d) ((d1 d).2.1 hd) hy' (Subgroup.centralizer {γ}) (fun c => by`. Rewrite using `[Subgroup.mem_centralizer_singleton_iff]`.

Express the relevant statement in the definitionally equal form `_ ↔ c⁻¹ * γ * c = γ`. Rewrite using `[mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]) μγ hμγ`. Simplify using `only [hsg] at oE`. Establish `hdiv : ∀ u : Fin n → kˣ, nrmT k d * sgT (RingEquiv.refl k) u / u = nrmT k d` using `fun u => mul_div_cancel_right _ u`. Distinguish the cases in `hmem : nrmT k d ∈ nrmSet k r t`.

Take `⟨u₀, hu₀⟩` from `(d2 r d t).2 hmem`. Establish `e1` using `oE (R.image (u₀ * ·)) (fun u => by`. Establish `e : d * sgT σ u / u / t = d * sgT σ u₀ / u₀ / t * (sgT σ (u₀⁻¹ * u) / (u₀⁻¹ * u))`. Establish `hm' : sgT (σ : E ≃+* E) (u₀⁻¹ * u) = (sgT (σ : E ≃+* E) u₀)⁻¹ * sgT (σ : E ≃+* E) u`. Use function extensionality and compare the values at `i`.

Simplify using `only [sgT, Pi.mul_apply, Pi.inv_apply, map_mul, map_inv]`. Rewrite using `[hm']`. Conclude with `alg _ _ _ _ _ _`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, rfl, hu⟩`.

Establish `h1` using `(hnear _ _ (hnear _ _ hu₀ hu₀).2 hu).1`. Rewrite `h1` using `[e, inv_mul_cancel_left]`. Take `⟨ρ, hρ, h2⟩` from `(hR1 _).1 h1`. Conclude with `⟨u₀ * ρ, Finset.mem_image_of_mem _ hρ, by simpa using (hR3 u₀ _ _).2 h2⟩`. Introduce and unpack `⟨_, hρ, h2⟩`.

Take `⟨ρ, hρ', rfl⟩` from `Finset.mem_image.1 hρ`. Use `⟨t, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `(hnear _ _ hu₀ ((hR1 _).2 ⟨ρ, hρ', (hR3 u₀ _ _).1 (by simpa using h2)⟩)).1)`. Use the proof step `(by`.

Introduce `a ha b hb hab`. Take `⟨a, ha', rfl⟩` from `Finset.mem_image.1 ha`. Take `⟨b, hb', rfl⟩` from `Finset.mem_image.1 hb`. Rewrite using `[hR2 a ha' b hb' ((hR3 _ _ _).1 hab)])`. Establish `n1 : Near r' (1 : Fin n → kˣ)` using `fun i => by simp`.

Establish `e2` using `ok {1} (fun u => ⟨fun _ => ⟨1, Finset.mem_singleton_self _, u, 1, rfl, n1, by simp⟩, fun _ => ⟨_, hmem, by rw [hdiv, div_self']; exact n1⟩⟩) (by simp)`. Rewrite `e1` using `[Finset.card_image_of_injective _ (mul_right_injective u₀)]`. Establish `hmeas : MeasurableSet {z : GL (Fin n) E | y⁻¹ * (h * z * h⁻¹) * y ∈ ball n r}` using `((hK ▸ hKo : IsOpen (ball n r)).preimage (by fun_prop)).measurableSet`. Establish `v1` using `congrArg (fun m : Measure (GL (Fin n) E) => m {z | y⁻¹ * (h * z * h⁻¹) * y ∈ ball n r}) hm`. Rewrite `v1` using `[Measure.map_apply (Continuous.measurable (by fun_prop)) hmeas, Measure.map_apply (f := fun t : Subgroup.centralizer {γ} => (incl (t : GL (Fin n) k) : GL (Fin n) E)) (hcl.continuous.comp continuous_subtype_val).measurable hmeas]`.

Establish `v2 : μδ.real {x : twCent (sigmaGL σ) δ | y⁻¹ * x * y ∈ ball n r} = j * μγ.real {x | y'⁻¹ * (x : GL (Fin n) k) * y' ∈ ball n r'}`. Rewrite using `[← hvol γ y' _ ((d1 d).2.1 hd) hy' μγ hμγ]`. Unfold `Measure.real`. Use `congr 1`. Use `v1 using 2` and compare the differences between its conclusion and the goal.

Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage]`. Rewrite using `[show h * (h⁻¹ * (x : GL (Fin n) E) * h) * h⁻¹ = x by group]`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage]`.

Rewrite using `[hal _ x.2]`. Use `e1.trans ?_` and prove the remaining obligations. Rewrite using `[show quotIntegral μk _ μγ (fun g => (elemSet r' (nrmSet k r t)).indicator 1 (g⁻¹ * γ * g)) = _ from e2]`. Rewrite using `[v2, ← Complex.ofReal_mul]`. Use `congr 1`.

Rewrite using `[Finset.card_singleton, Nat.cast_one, one_mul, div_mul_div_comm, mul_right_comm j, mul_div_mul_right _ _ pk.ne']`. Establish `e1` using `oE ∅ (fun u => ⟨fun ⟨_, hx, hu⟩ => absurd ((d2 r d t).1 ⟨u, hx ▸ hu⟩) hmem, by simp⟩) (by simp)`. Establish `e2` using `ok ∅ (fun u => ⟨fun ⟨x, hx, hu⟩ => absurd (by`. Rewrite `hu` using `[hdiv]`. Simplify using `using key x hx _ hu) hmem, by simp⟩) (by simp)`.

Use `e1.trans ?_` and prove the remaining obligations. Rewrite using `[show quotIntegral μk _ μγ (fun g => (elemSet r' (nrmSet k r t)).indicator 1 (g⁻¹ * γ * g)) = _ from e2]`. Simplify using the standard rewrite rules. Rewrite using `[quot_zero, quot_zero, mul_zero]`. Introduce `g`.

Use `Set.indicator_of_notMem (fun hg => hcase ?_) _` and prove the remaining obligations. Take `⟨d, hd, hnm⟩` from `meet' γ g hg`. Establish `hγ : IsRegSemisimple γ`. Establish `e : ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly = (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E)`. Rewrite using `[hNm, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, ← Matrix.charpoly_map]`.

Both sides reduce to the same expression. Unfold `IsTwRegSemisimple at hδ`. Rewrite `hδ` using `[e]`. Conclude with `(Polynomial.separable_map _).1 hδ`. Take `⟨x, hx⟩` from `normInj k E σ hσ n γ hγ δ _ ⟨h, hNm⟩ hnm`.

Conclude with `⟨x, d, hd, hx.symm⟩`. Introduce `g`. Use `Set.indicator_of_notMem (fun hg => hcase ?_) _` and prove the remaining obligations. Take `⟨y, x, -, s, -, hs, e⟩` from `(hS E n σ _ hcyc r hr0 hr1 _ hA1).1 δ g (by rw [hsg]; exact hg)`. Conclude with `⟨y, _, hs, by rw [← hsg]; exact e⟩`.

Use `quot_zero _ _ _ _ fun g => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Set.indicator_of_notMem (fun hg => hnn ?_), smul_zero]`. Take `⟨d, -, hnm⟩` from `meet' γ g hg`. Conclude with `⟨_, hnm⟩`.
-/
theorem elemLoc_of (hS : SuppE) (hO : OneField) (hR : Reps) (hN : NormOpen) (hD : NormDiag) (hA : Align) (hV : VolRatio)
    (hB : ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ)
      (r : ValueGroupWithZero E), 0 < r → r < 1 → ∃ K : Subgroup (GL (Fin n) E), (K : Set (GL (Fin n) E)) = ball n r ∧
        IsOpen (K : Set (GL (Fin n) E)) ∧ IsCompact (K : Set (GL (Fin n) E))) : ElemLoc := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ n _ _ _ _ μE μk hE hk r hr0 hr1
  obtain ⟨r₀, h00, h01, hn⟩ := hN k E σ hσ r hr0 hr1
  refine ⟨r₀, h00, h01, fun r' hle h'0 => ⟨fun x hx => (hn x (hx.trans hle)).2, ?_⟩⟩
  have h'1 : r' < 1 := hle.trans_lt h01
  obtain ⟨hcyc, -, hbr⟩ := bridge k E σ
  obtain ⟨hsg, -, -, hcl, -⟩ := hbr n
  have hc1 : Cyc (RingEquiv.refl k) 1 := ⟨fun _ => rfl, one_pos, fun _ => rfl⟩
  obtain ⟨R, hRne, hR1, hR2, hnear, hR3⟩ := hR E n σ _ hcyc r hr0 hr1
  obtain ⟨j, hj, hvol⟩ := hV k E σ hσ n r r' hr0 hr1 h'0 h'1 fun x hx => (hn x (hx.trans hle)).1
  obtain ⟨d1, d2, d3⟩ := hD k E σ hσ n
  obtain ⟨K, hK, hKo, hKc⟩ := hB E n r hr0 hr1
  obtain ⟨K', hK', hKo', hKc'⟩ := hB k n r' h'0 h'1
  obtain ⟨a1, a2, a3, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop E n
  have pE : 0 < μE.real (ball n r) := hK ▸ ENNReal.toReal_pos (hKo.measure_ne_zero μE ⟨1, one_mem _⟩) hKc.measure_ne_top
  have pk : 0 < μk.real (ball n r') := hK' ▸ ENNReal.toReal_pos (hKo'.measure_ne_zero μk ⟨1, one_mem _⟩) hKc'.measure_ne_top
  have pR : (0 : ℝ) < R.card := Nat.cast_pos.2 hRne.card_pos
  refine ⟨R.card * μE.real (ball n r) / (j * μk.real (ball n r')), by positivity, fun t ht => ?_⟩
  have hA1 : ∀ x ∈ ({t} : Set (Fin n → Eˣ)), Strict x := fun x hx => hx ▸ ht
  have hA2 := (d3 r hr1 t ht).1
  have key : ∀ x ∈ nrmSet k r t, ∀ s, Near r' s → x * s ∈ nrmSet k r t := by
    rintro _ ⟨u, hu, rfl⟩ s hs
    choose u' hu' hu'' using fun i => (hn (s i) ((hs i).trans hle)).2
    refine ⟨u * u', (hnear u u' hu hu').1, funext fun i => Units.ext ?_⟩
    simp only [nrmT, Pi.mul_apply, Units.val_mul, Units.coe_map, map_mul, hu'', mul_assoc]
  obtain ⟨-, -, -, -, hnear', -⟩ := hR k n _ _ hc1 r' h'0 h'1
  have meet' : ∀ γ g : GL (Fin n) k, g⁻¹ * γ * g ∈ elemSet r' (nrmSet k r t) →
      ∃ d : Fin n → Eˣ, Strict d ∧ IsNormOf σ (diagT E (Fin n) d) γ := fun γ g hg => by
    obtain ⟨y, x, hx, s, hs, -, e⟩ := (hS k n _ _ hc1 r' h'0 h'1 _ hA2).1 γ g hg
    obtain ⟨u, hu, e'⟩ := key x hx s hs
    refine ⟨t * u, fun i i' h => ?_, (incl y)⁻¹, ?_⟩
    · have hv : ∀ i, valuation E (u i : E) = 1 := fun i => by
        have := Valuation.map_one_add_of_lt (valuation E) ((hu i).trans_lt hr1)
        rwa [add_sub_cancel] at this
      simpa [hv] using ht i i' h
    · rw [(d1 _).1, ← e', ← e, inv_inv, map_mul, map_mul, map_inv]
      rfl
  refine ⟨fun δ γ h μδ μγ hδ hNm hμδ hμγ hm => ?_, fun γ μγ hγ hnn hμ => ?_⟩
  · unfold twOrbIntegralC orbIntegralC
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [quot_smul]
    by_cases hcase : ∃ y d, Strict d ∧ y⁻¹ * δ * sigmaGL σ y = diagT E (Fin n) d
    · obtain ⟨y, d, hd, hy⟩ := hcase
      obtain ⟨y', hy', hal⟩ := hA k E σ hσ n δ h y γ d hd hNm hy
      have oE := hO E n σ _ hcyc r hr0 hr1 μE hE _ hA1 δ y d hd (by rw [hsg]; exact hy) (twCent (sigmaGL σ) δ)
        (fun c => by rw [hsg]; rfl) μδ hμδ
      have ok := hO k n _ _ hc1 r' h'0 h'1 μk hk _ hA2 γ y' (nrmT k d) ((d1 d).2.1 hd) hy' (Subgroup.centralizer {γ})
        (fun c => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          change _ ↔ c⁻¹ * γ * c = γ
          rw [mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]) μγ hμγ
      simp only [hsg] at oE
      have hdiv : ∀ u : Fin n → kˣ, nrmT k d * sgT (RingEquiv.refl k) u / u = nrmT k d := fun u => mul_div_cancel_right _ u
      by_cases hmem : nrmT k d ∈ nrmSet k r t
      · obtain ⟨u₀, hu₀⟩ := (d2 r d t).2 hmem
        have e1 := oE (R.image (u₀ * ·)) (fun u => by
          have e : d * sgT σ u / u / t = d * sgT σ u₀ / u₀ / t * (sgT σ (u₀⁻¹ * u) / (u₀⁻¹ * u)) := by
            have hm' : sgT (σ : E ≃+* E) (u₀⁻¹ * u) = (sgT (σ : E ≃+* E) u₀)⁻¹ * sgT (σ : E ≃+* E) u := by
              funext i
              simp only [sgT, Pi.mul_apply, Pi.inv_apply, map_mul, map_inv]
            rw [hm']
            exact alg _ _ _ _ _ _
          constructor
          · rintro ⟨_, rfl, hu⟩
            have h1 := (hnear _ _ (hnear _ _ hu₀ hu₀).2 hu).1
            rw [e, inv_mul_cancel_left] at h1
            obtain ⟨ρ, hρ, h2⟩ := (hR1 _).1 h1
            exact ⟨u₀ * ρ, Finset.mem_image_of_mem _ hρ, by simpa using (hR3 u₀ _ _).2 h2⟩
          · rintro ⟨_, hρ, h2⟩
            obtain ⟨ρ, hρ', rfl⟩ := Finset.mem_image.1 hρ
            refine ⟨t, rfl, ?_⟩
            rw [e]
            exact (hnear _ _ hu₀ ((hR1 _).2 ⟨ρ, hρ', (hR3 u₀ _ _).1 (by simpa using h2)⟩)).1)
          (by
            intro a ha b hb hab
            obtain ⟨a, ha', rfl⟩ := Finset.mem_image.1 ha
            obtain ⟨b, hb', rfl⟩ := Finset.mem_image.1 hb
            rw [hR2 a ha' b hb' ((hR3 _ _ _).1 hab)])
        have n1 : Near r' (1 : Fin n → kˣ) := fun i => by simp
        have e2 := ok {1} (fun u => ⟨fun _ => ⟨1, Finset.mem_singleton_self _, u, 1, rfl, n1, by simp⟩,
          fun _ => ⟨_, hmem, by rw [hdiv, div_self']; exact n1⟩⟩) (by simp)
        rw [Finset.card_image_of_injective _ (mul_right_injective u₀)] at e1
        have hmeas : MeasurableSet {z : GL (Fin n) E | y⁻¹ * (h * z * h⁻¹) * y ∈ ball n r} :=
          ((hK ▸ hKo : IsOpen (ball n r)).preimage (by fun_prop)).measurableSet
        have v1 := congrArg (fun m : Measure (GL (Fin n) E) => m {z | y⁻¹ * (h * z * h⁻¹) * y ∈ ball n r}) hm
        rw [Measure.map_apply (Continuous.measurable (by fun_prop)) hmeas,
          Measure.map_apply (f := fun t : Subgroup.centralizer {γ} => (incl (t : GL (Fin n) k) : GL (Fin n) E))
            (hcl.continuous.comp continuous_subtype_val).measurable hmeas] at v1
        have v2 : μδ.real {x : twCent (sigmaGL σ) δ | y⁻¹ * x * y ∈ ball n r} =
            j * μγ.real {x | y'⁻¹ * (x : GL (Fin n) k) * y' ∈ ball n r'} := by
          rw [← hvol γ y' _ ((d1 d).2.1 hd) hy' μγ hμγ]
          unfold Measure.real
          congr 1
          convert v1 using 2
          · ext x
            simp only [Set.mem_setOf_eq, Set.mem_preimage]
            rw [show h * (h⁻¹ * (x : GL (Fin n) E) * h) * h⁻¹ = x by group]
          · ext x
            simp only [Set.mem_setOf_eq, Set.mem_preimage]
            rw [hal _ x.2]
        refine e1.trans ?_
        rw [show quotIntegral μk _ μγ (fun g => (elemSet r' (nrmSet k r t)).indicator 1 (g⁻¹ * γ * g)) = _ from e2]
        rw [v2, ← Complex.ofReal_mul]
        congr 1
        rw [Finset.card_singleton, Nat.cast_one, one_mul, div_mul_div_comm, mul_right_comm j, mul_div_mul_right _ _ pk.ne']
      · have e1 := oE ∅ (fun u => ⟨fun ⟨_, hx, hu⟩ => absurd ((d2 r d t).1 ⟨u, hx ▸ hu⟩) hmem, by simp⟩) (by simp)
        have e2 := ok ∅ (fun u => ⟨fun ⟨x, hx, hu⟩ => absurd (by
          rw [hdiv] at hu
          simpa using key x hx _ hu) hmem, by simp⟩) (by simp)
        refine e1.trans ?_
        rw [show quotIntegral μk _ μγ (fun g => (elemSet r' (nrmSet k r t)).indicator 1 (g⁻¹ * γ * g)) = _ from e2]
        simp
    · rw [quot_zero, quot_zero, mul_zero]
      · intro g
        refine Set.indicator_of_notMem (fun hg => hcase ?_) _
        obtain ⟨d, hd, hnm⟩ := meet' γ g hg
        have hγ : IsRegSemisimple γ := by
          have e : ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
              (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) := by
            rw [hNm, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, ← Matrix.charpoly_map]
            rfl
          unfold IsTwRegSemisimple at hδ
          rw [e] at hδ
          exact (Polynomial.separable_map _).1 hδ
        obtain ⟨x, hx⟩ := normInj k E σ hσ n γ hγ δ _ ⟨h, hNm⟩ hnm
        exact ⟨x, d, hd, hx.symm⟩
      · intro g
        refine Set.indicator_of_notMem (fun hg => hcase ?_) _
        obtain ⟨y, x, -, s, -, hs, e⟩ := (hS E n σ _ hcyc r hr0 hr1 _ hA1).1 δ g (by rw [hsg]; exact hg)
        exact ⟨y, _, hs, by rw [← hsg]; exact e⟩
  · refine quot_zero _ _ _ _ fun g => ?_
    rw [Pi.smul_apply, Set.indicator_of_notMem (fun hg => hnn ?_), smul_zero]
    obtain ⟨d, -, hnm⟩ := meet' γ g hg
    exact ⟨_, hnm⟩

end UpperTheory.Gal.InertialTypesAlt.L
