import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

/- English proof (translation)
Introduce `G V _ _ _ _ _ _ μ _ _ _ _ π hπ K hK e he x`. Establish `hfx : ∀ {v : V}, v ∈ fixed π K ↔ ∀ k ∈ K, π k v = v` using `GlobalTheory.IwahoriInj.mem_fixed`. Use `set D : Set G := {g | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} with hDdef`. Establish `hDc : IsCompact D`. Use `(hK.1.prod hK.1).image (f := fun y : G × G => y.1 * x * y.2) (by fun_prop) using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `g`. Conclude with `⟨fun ⟨a, ha, b, hb, h⟩ => ⟨(a, b), ⟨ha, hb⟩, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y.1, hy.1, y.2, hy.2, h.symm⟩⟩`. Establish `hDm : MeasurableSet D` using `hDc.measurableSet`. Establish `hL : ∀ k ∈ K, ∀ g, k * g ∈ D ↔ g ∈ D`. Establish `h1 : ∀ k ∈ K, ∀ g, g ∈ D → k * g ∈ D`.

Introduce and unpack `k hk _ ⟨a, ha, b, hb, rfl⟩`. Conclude with `⟨k * a, mul_mem hk ha, b, hb, by simp only [mul_assoc]⟩`. Use `fun k hk g => ⟨fun h => ?_, h1 k hk g⟩` and prove the remaining obligations. Simplify using `using h1 _ (inv_mem hk) _ h`. Establish `hR : ∀ k ∈ K, ∀ g, g * k ∈ D ↔ g ∈ D`.

Establish `h1 : ∀ k ∈ K, ∀ g, g ∈ D → g * k ∈ D`. Introduce and unpack `k hk _ ⟨a, ha, b, hb, rfl⟩`. Conclude with `⟨a, ha, b * k, mul_mem hb hk, by simp only [mul_assoc]⟩`. Use `fun k hk g => ⟨fun h => ?_, h1 k hk g⟩` and prove the remaining obligations. Simplify using `using h1 _ (inv_mem hk) _ h`.

Take `⟨A, hA⟩` from `GlobalTheory.IwahoriTraceProof.exists_setOp μ hπ hDc hDm`. Establish `hsep : ∀ y z : V, (∀ l : Module.Dual ℂ V, l y = l z) → y = z` using `fun y z h => by`. Rewrite using `[← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `l`. Rewrite using `[map_sub, h l, sub_self]`.

Establish `hAr : ∀ k ∈ K, ∀ v, A (π k v) = A v` using `fun k hk v => hsep _ _ fun l => by`. Rewrite using `[(hA _ l).2, (hA v l).2, ← integral_indicator hDm, ← integral_indicator hDm, ← integral_mul_right_eq_self (D.indicator fun g => l (π g v)) k]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Distinguish the cases in `h : g ∈ D`.

Simplify using `[h, (hR k hk g).2 h]`. Establish `h' : g * k ∉ D` using `fun h' => h ((hR k hk g).1 h')`. Simplify using `[h, h']`. Establish `hAl : ∀ k ∈ K, ∀ v, π k (A v) = A v` using `fun k hk v => hsep _ _ fun l => by`. Establish `h0` using `(hA v (l ∘ₗ π k)).2`.

Rewrite `h0` using `[LinearMap.comp_apply]`. Rewrite using `[h0, (hA v l).2, ← integral_indicator hDm, ← integral_indicator hDm, ← integral_mul_left_eq_self (D.indicator fun g => l (π g v)) k]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Distinguish the cases in `h : g ∈ D`.

Simplify using `[h, (hL k hk g).2 h]`. Establish `h' : k * g ∉ D` using `fun h' => h ((hL k hk g).1 h')`. Simplify using `[h, h']`. Establish `hAe : ∀ v, A (e v) = A v` using `fun v => he.lin V A v fun k hk => hAr k hk v`. Establish `heA : ∀ v, e (A v) = A v` using `fun v => he.fix _ (hfx.2 fun k hk => hAl k hk v)`.

Establish `hval : ∀ v, A v = (μ.real D : ℂ) • e (π x (e v))` using `fun v => hsep _ _ fun l => by`. Establish `hw : ∀ k ∈ K, π k (e v) = e v` using `hfx.1 (he.mem v)`. Establish `h0` using `(hA (e v) (l ∘ₗ e)).2`. Rewrite `h0` using `[LinearMap.comp_apply, heA, hAe]`. Rewrite using `[h0, map_smul, smul_eq_mul, setIntegral_congr_fun (g := fun _ => l (e (π x (e v)))) hDm fun g hg => ?_]`.

Simplify using `[Measure.real]`. Take `⟨a, ha, b, hb, rfl⟩` from `hg`. Simplify using `only [LinearMap.comp_apply, map_mul, Module.End.mul_apply, hw b hb, he.inv a ha]`. Introduce `v l`. Establish `hind : (fun g => D.indicator (fun _ => (1 : ℂ)) g * l (π g v)) = D.indicator fun g => l (π g v)`.

Use function extensionality and compare the values at `g`. Apply the tactic sequence `by_cases h : g ∈ D <;> simp [h]`. Rewrite using `[hind]`. Use `⟨(integrable_indicator_iff hDm).2 (hA v l).1, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_indicator hDm, ← (hA v l).2, hval v]`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.Join.dcosOp :
    UpperTheory.Gal.Join.DcosOp := by
  intro G V _ _ _ _ _ _ μ _ _ _ _ π hπ K hK e he x
  have hfx : ∀ {v : V}, v ∈ fixed π K ↔ ∀ k ∈ K, π k v = v := GlobalTheory.IwahoriInj.mem_fixed
  set D : Set G := {g | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} with hDdef
  have hDc : IsCompact D := by
    convert (hK.1.prod hK.1).image (f := fun y : G × G => y.1 * x * y.2) (by fun_prop) using 1
    ext g
    exact ⟨fun ⟨a, ha, b, hb, h⟩ => ⟨(a, b), ⟨ha, hb⟩, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y.1, hy.1, y.2, hy.2, h.symm⟩⟩
  have hDm : MeasurableSet D := hDc.measurableSet
  have hL : ∀ k ∈ K, ∀ g, k * g ∈ D ↔ g ∈ D := by
    have h1 : ∀ k ∈ K, ∀ g, g ∈ D → k * g ∈ D := by
      rintro k hk _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨k * a, mul_mem hk ha, b, hb, by simp only [mul_assoc]⟩
    refine fun k hk g => ⟨fun h => ?_, h1 k hk g⟩
    simpa using h1 _ (inv_mem hk) _ h
  have hR : ∀ k ∈ K, ∀ g, g * k ∈ D ↔ g ∈ D := by
    have h1 : ∀ k ∈ K, ∀ g, g ∈ D → g * k ∈ D := by
      rintro k hk _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, mul_mem hb hk, by simp only [mul_assoc]⟩
    refine fun k hk g => ⟨fun h => ?_, h1 k hk g⟩
    simpa using h1 _ (inv_mem hk) _ h
  obtain ⟨A, hA⟩ := GlobalTheory.IwahoriTraceProof.exists_setOp μ hπ hDc hDm
  have hsep : ∀ y z : V, (∀ l : Module.Dual ℂ V, l y = l z) → y = z := fun y z h => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, h l, sub_self]
  have hAr : ∀ k ∈ K, ∀ v, A (π k v) = A v := fun k hk v => hsep _ _ fun l => by
    rw [(hA _ l).2, (hA v l).2, ← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_right_eq_self (D.indicator fun g => l (π g v)) k]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, (hR k hk g).2 h]
    · have h' : g * k ∉ D := fun h' => h ((hR k hk g).1 h')
      simp [h, h']
  have hAl : ∀ k ∈ K, ∀ v, π k (A v) = A v := fun k hk v => hsep _ _ fun l => by
    have h0 := (hA v (l ∘ₗ π k)).2
    rw [LinearMap.comp_apply] at h0
    rw [h0, (hA v l).2, ← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_left_eq_self (D.indicator fun g => l (π g v)) k]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, (hL k hk g).2 h]
    · have h' : k * g ∉ D := fun h' => h ((hL k hk g).1 h')
      simp [h, h']
  have hAe : ∀ v, A (e v) = A v := fun v => he.lin V A v fun k hk => hAr k hk v
  have heA : ∀ v, e (A v) = A v := fun v => he.fix _ (hfx.2 fun k hk => hAl k hk v)
  have hval : ∀ v, A v = (μ.real D : ℂ) • e (π x (e v)) := fun v => hsep _ _ fun l => by
    have hw : ∀ k ∈ K, π k (e v) = e v := hfx.1 (he.mem v)
    have h0 := (hA (e v) (l ∘ₗ e)).2
    rw [LinearMap.comp_apply, heA, hAe] at h0
    rw [h0, map_smul, smul_eq_mul,
      setIntegral_congr_fun (g := fun _ => l (e (π x (e v)))) hDm fun g hg => ?_]
    · simp [Measure.real]
    · obtain ⟨a, ha, b, hb, rfl⟩ := hg
      simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply, hw b hb, he.inv a ha]
  intro v l
  have hind : (fun g => D.indicator (fun _ => (1 : ℂ)) g * l (π g v)) = D.indicator fun g => l (π g v) := by
    funext g
    by_cases h : g ∈ D <;> simp [h]
  rw [hind]
  refine ⟨(integrable_indicator_iff hDm).2 (hA v l).1, ?_⟩
  rw [integral_indicator hDm, ← (hA v l).2, hval v]
  rfl
