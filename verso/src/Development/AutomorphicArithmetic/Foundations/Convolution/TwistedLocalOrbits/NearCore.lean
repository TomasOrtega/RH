import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bridge
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NormInj
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ConjDesc
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OrbProper
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.QuotDesc
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.TwOrbConj
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RootEx
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RootConj
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RigidNear
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OpenNear
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ValuationNatCastLeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ExtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.CentComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Unimod
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Untwist

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc.NearIdentityCentralizer

open UpperTheory.ConvolutionTheory.Loc.BallG

/- English proof (translation)
Simplify using `[quotIntegral, h]`.
-/
private theorem quot_zero {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (H : Subgroup G) (ν : Measure H) {F : G → ℂ}
    (h : ∀ g, F g = 0) : quotIntegral μ H ν F = 0 := by
  simp [quotIntegral, h]

section Alg

variable {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ}

/- English proof (translation)
Introduce `x y h` and use `by ext i j exact (algebraMap k E).injective (congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j) h)`.
-/
private theorem incl_inj : Function.Injective (incl : GL (Fin n) k → GL (Fin n) E) := fun x y h => by
  ext i j
  exact (algebraMap k E).injective (congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j) h)

/- English proof (translation)
Use extensionality with `i j`. Conclude with `σ.commutes _`.
-/
private theorem sigma_incl (σ : E ≃ₐ[k] E) (y : GL (Fin n) k) : sigmaGL σ (incl y : GL (Fin n) E) = incl y := by
  ext i j
  exact σ.commutes _

/- English proof (translation)
Unfold `normGL`. Proceed by induction on `Module.finrank k E with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[twNorm_succ, ih, pow_succ y, map_mul]`.

Use `congr 1`. Use `clear ih`. Proceed by induction on `m with`. Consider the case `zero => rfl`. Consider the case `succ m ih => rw [pow_succ_apply, sigma_incl, ih]`.
-/
private theorem norm_incl (σ : E ≃ₐ[k] E) (y : GL (Fin n) k) :
    normGL σ (incl y : GL (Fin n) E) = incl (y ^ Module.finrank k E) := by
  unfold normGL
  induction Module.finrank k E with
  | zero => simp
  | succ m ih =>
    rw [twNorm_succ, ih, pow_succ y, map_mul]
    congr 1
    clear ih
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ_apply, sigma_incl, ih]

/- English proof (translation)
Establish `e : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (γ : Matrix (Fin n) (Fin n) k).map (algebraMap k E)` using `rfl`. Rewrite using `[e, Matrix.charpoly_map, Polynomial.separable_map]`. Both sides reduce to the same expression.
-/
private theorem sep_incl (γ : GL (Fin n) k) :
    ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable ↔ IsRegSemisimple γ := by
  have e : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (γ : Matrix (Fin n) (Fin n) k).map (algebraMap k E) := rfl
  rw [e, Matrix.charpoly_map, Polynomial.separable_map]
  rfl

/- English proof (translation)
Rewrite using `[Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]`.
-/
private theorem sep_conj (x h : GL (Fin n) E) : ((h * x * h⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
    (x : Matrix (Fin n) (Fin n) E).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

/- English proof (translation)
The claim follows from `Units.ext (UpperTheory.V.Z.Tf.Orb.centComm E n a x y ha (congrArg Units.val hx) (congrArg Units.val hy))`.
-/
private theorem comm_of_sep {a x y : GL (Fin n) E} (ha : (a : Matrix (Fin n) (Fin n) E).charpoly.Separable)
    (hx : x * a = a * x) (hy : y * a = a * y) : x * y = y * x :=
  Units.ext (UpperTheory.V.Z.Tf.Orb.centComm E n a x y ha (congrArg Units.val hx) (congrArg Units.val hy))

/- English proof (translation)
Rewrite using `[← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]`.
-/
private theorem theta_pow [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E) :
    (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
  rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]

/- English proof (translation)
Rewrite using `[mem_twCent, mem_twCent, twConj, map_mul, map_mul, map_inv]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Combine the equalities or inequalities in the displayed calculation. Introduce `h`.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem mem_twCent_conj {G : Type} [Group G] (θ : Monoid.End G) (δ g x : G) :
    x ∈ twCent θ δ ↔ g⁻¹ * x * g ∈ twCent θ (twConj θ g δ) := by
  rw [mem_twCent, mem_twCent, twConj, map_mul, map_mul, map_inv]
  constructor
  · intro h
    calc _ = g⁻¹ * (x⁻¹ * δ * θ x) * θ g := by group
      _ = _ := by rw [h]
  · intro h
    calc _ = g * ((g⁻¹ * x * g)⁻¹ * (g⁻¹ * δ * θ g) * ((θ g)⁻¹ * θ x * θ g)) * (θ g)⁻¹ := by group
      _ = _ := by rw [h]; group

end Alg

section Loc

variable {k E : Type} [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] {σ : E ≃ₐ[k] E}
  (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) {n : ℕ} {r : ValueGroupWithZero E}
  (hr : r < valuation E (Module.finrank k E : E))

include hr in
/- English proof (translation)
Apply `incl_inj (E := E)` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, map_inv]`. Use `rootConj E n _ r hr _ hu _ hu' _ ?_` and prove the remaining obligations. Rewrite using `[← map_pow, ← map_pow, ← h, map_mul, map_mul, map_inv]`.
-/
private theorem root_conj {u u' y : GL (Fin n) k} (hu : (incl u : GL (Fin n) E) ∈ ball n r) (hu' : (incl u' : GL (Fin n) E) ∈ ball n r)
    (h : y⁻¹ * u ^ Module.finrank k E * y = u' ^ Module.finrank k E) : y⁻¹ * u * y = u' := by
  apply incl_inj (E := E)
  rw [map_mul, map_mul, map_inv]
  refine rootConj E n _ r hr _ hu _ hu' _ ?_
  rw [← map_pow, ← map_pow, ← h, map_mul, map_mul, map_inv]

include hgen hr in
/- English proof (translation)
Take `⟨hc, -, hb⟩` from `bridge k E σ`. Take `⟨x, hx⟩` from `((hb n).2.2.1 hgen ((incl y)⁻¹ * g * incl y')).mp (rigidNear E n σ _ hc r hr _ hu _ hu' (sigma_incl σ u) (sigma_incl σ u') _ (by show _ * _ * sigmaGL σ _ = _`. Simplify using `only [map_mul, map_inv, sigma_incl] at h ⊢`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨y * x * y'⁻¹, by rw [map_mul, map_mul, map_inv, hx]; group⟩`.
-/
private theorem rigid {u u' y y' : GL (Fin n) k} (hu : (incl u : GL (Fin n) E) ∈ ball n r) (hu' : (incl u' : GL (Fin n) E) ∈ ball n r)
    {g : GL (Fin n) E} (h : g⁻¹ * incl (y * u * y⁻¹) * sigmaGL σ g = incl (y' * u' * y'⁻¹)) : ∃ x : GL (Fin n) k, incl x = g := by
  obtain ⟨hc, -, hb⟩ := bridge k E σ
  obtain ⟨x, hx⟩ := ((hb n).2.2.1 hgen ((incl y)⁻¹ * g * incl y')).mp
    (rigidNear E n σ _ hc r hr _ hu _ hu' (sigma_incl σ u) (sigma_incl σ u') _ (by
      show _ * _ * sigmaGL σ _ = _
      simp only [map_mul, map_inv, sigma_incl] at h ⊢
      calc _ = (incl y')⁻¹ * (g⁻¹ * (incl y * incl u * (incl y)⁻¹) * sigmaGL σ g) * incl y' := by group
        _ = _ := by rw [h]; group))
  exact ⟨y * x * y'⁻¹, by rw [map_mul, map_mul, map_inv, hx]; group⟩

include hgen hr in
/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_twCent, Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨x, rfl⟩` from `rigid hgen hr hu hu h`.

Use `⟨x, ?_, rfl⟩` and prove the remaining obligations. Rewrite `h` using `[sigma_incl, ← map_inv, ← map_mul, ← map_mul]`. Establish `h1` using `incl_inj h`. Rewrite using `[Subgroup.mem_centralizer_singleton_iff, ← conj_pow]`. Use `(Commute.pow_right ?_ _).eq` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨x, hx, rfl⟩`. Rewrite `hx` using `[Subgroup.mem_centralizer_singleton_iff]`. Establish `h1` using `root_conj hr hu hu (y := y⁻¹ * x * y) (by`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[sigma_incl, ← map_inv, ← map_mul, ← map_mul]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem cent_eq {u : GL (Fin n) k} (hu : (incl u : GL (Fin n) E) ∈ ball n r) (y : GL (Fin n) k) :
    twCent (sigmaGL σ) (incl (y * u * y⁻¹) : GL (Fin n) E) =
      (Subgroup.centralizer {y * u ^ Module.finrank k E * y⁻¹}).map incl := by
  ext x
  rw [mem_twCent, Subgroup.mem_map]
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := rigid hgen hr hu hu h
    refine ⟨x, ?_, rfl⟩
    rw [sigma_incl, ← map_inv, ← map_mul, ← map_mul] at h
    have h1 := incl_inj h
    rw [Subgroup.mem_centralizer_singleton_iff, ← conj_pow]
    refine (Commute.pow_right ?_ _).eq
    calc x * (y * u * y⁻¹) = x * (x⁻¹ * (y * u * y⁻¹) * x) := by rw [h1]
      _ = _ := by group
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have h1 := root_conj hr hu hu (y := y⁻¹ * x * y) (by
      calc _ = y⁻¹ * x⁻¹ * (y * u ^ Module.finrank k E * y⁻¹ * x) * y := by group
        _ = _ := by rw [← hx]; group)
    rw [sigma_incl, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    calc _ = y * ((y⁻¹ * x * y)⁻¹ * u * (y⁻¹ * x * y)) * y⁻¹ := by group
      _ = _ := by rw [h1]

end Loc

end UpperTheory.ConvolutionTheory.Loc.NearIdentityCentralizer

open UpperTheory.ConvolutionTheory.Loc.NearIdentityCentralizer UpperTheory.ConvolutionTheory.Loc.BallG UpperTheory.V.Z.Tf.Orb in

/- English proof (translation)
Introduce `k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n _ _ _ _ μE μk hμE hμk r hr K hK hKo hKc φ hφ f hf hs h2 h1`. Take `⟨hc, -, hb⟩` from `bridge k E σ`. Establish `hj` using `(hb n).2.2.2.1`. Take `⟨_, _, _, -⟩` from `gLTop E n`. Take `⟨_, _, _, -⟩` from `gLTop k n`.

Establish `hθ : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E)` using `((extCont k E).2.2 n).2 σ`. Establish `mem : ∀ {g : GL (Fin n) E}, g ∈ K ↔ g ∈ ball n r` using `fun {g} => by rw [← hK]; rfl`. Use `⟨fun δ γ h μδ μγ hδ hN hμδ hμγ hmap => ?_, fun γ μγ _ hno _ => ?_⟩` and prove the remaining obligations. Use `swap`. Use `quot_zero _ _ _ fun y => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `h0`. Take `⟨u, -, hu⟩` from `h2 _ h0`. Conclude with `hno ⟨incl u, (incl y)⁻¹, by rw [norm_incl, ← hu, map_mul, map_mul, map_inv, inv_inv]⟩`. Establish `hγE : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable`. Rewrite using `[← sep_conj _ h, ← hN]`.

Conclude with `hδ`. Establish `hγ : IsRegSemisimple γ` using `(sep_incl γ).mp hγE`. Distinguish the cases in `hex : ∃ u y : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r ∧ γ = y * u ^ Module.finrank k E * y⁻¹`. Use `swap`. Rewrite using `[twOrbIntegralC, orbIntegralC, quot_zero, quot_zero]`.

Introduce `y`. Assume the negation of the conclusion as `h0`. Take `⟨u, hu, e⟩` from `h2 _ h0`. Conclude with `hex ⟨u, y, mem.1 hu, by rw [← e]; group⟩`. Introduce `g`.

Assume the negation of the conclusion as `h0`. Take `⟨κ, -, u, hu, e⟩` from `hs _ h0`. Use `replace hu := mem.1 hu`. Establish `e1` using `congrArg (twNorm (sigmaGL σ) (Module.finrank k E)) e`. Rewrite `e1` using `[← twConj, twNorm_twConj_of_pow_eq_one _ (theta_pow σ), twNorm_twConj_of_pow_eq_one _ (theta_pow σ), ← normGL, ← normGL, hN, norm_incl]`.

Take `⟨y, hy⟩` from `conjDesc k E n γ (u ^ Module.finrank k E) hγ ⟨κ * g⁻¹ * h, by`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hex ⟨u, y⁻¹, hu, by rw [hy]; group⟩`. Take `⟨u, y, hu, hγu⟩` from `hex`. Establish `hN1 : normGL σ (incl (y * u * y⁻¹) : GL (Fin n) E) = incl γ` using `by rw [norm_incl, conj_pow, hγu]`.

Take `⟨g, hg⟩` from `normInj k E σ hgen n γ hγ δ (incl (y * u * y⁻¹)) ⟨h, hN⟩ ⟨1, by simpa using hN1⟩`. Take `⟨μ', hμ', hmap'⟩` from `haarConj (GL (Fin n) E) _ _ g (mem_twCent_conj (sigmaGL σ) δ g) μδ hμδ`. Rewrite using `[← twOrbConj k E σ n μE hμE δ g μδ μ' hδ hμδ hμ' hmap' φ hφ]`. Establish `hz : h⁻¹ * g * incl γ = incl γ * (h⁻¹ * g)`. Establish `e` using `hN1`.

Rewrite `e` using `[hg, normGL, twNorm_twConj_of_pow_eq_one _ (theta_pow σ), ← normGL, hN]`. Combine the equalities or inequalities in the displayed calculation. Establish `hpt : (fun x : twCent (sigmaGL σ) δ => g⁻¹ * (x : GL (Fin n) E) * g) = fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h`. Use function extensionality and compare the values at `x`. Establish `e` using `comm_of_sep hγE (Subgroup.mem_centralizer_singleton_iff.mp (conj_twCent_mem_centralizer _ (theta_pow σ) hN x.2)) hz`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `hmap'` using `[hpt, hmap]`. Use `clear hμ' hpt`. Use `revert μ'`. Rewrite using `[← hg]`.

Introduce `μ' hmap'`. Establish `hT : IsClosed (Subgroup.centralizer ({γ} : Set (GL (Fin n) k)) : Set (GL (Fin n) k))`. Establish `e : (Subgroup.centralizer ({γ} : Set (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x}` using `Set.ext fun x => Subgroup.mem_centralizer_singleton_iff`. Rewrite using `[e]`. Conclude with `isClosed_eq (by fun_prop) (by fun_prop)`.

Establish `hinv` using `(haarComm (GL (Fin n) k) _ hT (fun a ha b hb => comm_of_sep hγ (Subgroup.mem_centralizer_singleton_iff.mp ha) (Subgroup.mem_centralizer_singleton_iff.mp hb)) μγ hμγ).2.1`. Establish `hreg : IsTwRegSemisimple σ (incl (y * u * y⁻¹) : GL (Fin n) E)`. Rewrite using `[IsTwRegSemisimple, hN1]`. Conclude with `hγE`. Take `⟨D, hD, hDs⟩` from `orbProper k E σ hgen n _ hreg _ hφ.2`.

Use `haveI : ValuativeExtension k k := ⟨fun _ _ => Iff.rfl⟩`. Take `⟨a1, a2, a3, -⟩` from `untwist k n μk γ`. Take `⟨D', hD', hDs'⟩` from `orbProper k k 1 a1 n γ (a3 hγ) _ hf.2`. Establish `hKo' : IsOpen ((K.comap (incl : GL (Fin n) k →* GL (Fin n) E) : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k))` using `hKo.preimage hj.continuous`. Establish `hKc' : IsCompact ((K.comap (incl : GL (Fin n) k →* GL (Fin n) E) : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k))` using `hj.isCompact_preimage hKc`.

Rewrite using `[twOrbIntegralC, quotDesc _ _ incl hj μE μk hμE (unimod gLTop E n μE hμE).1 hμk (unimod gLTop k n μk hμk).1 K hKo hKc _ _ μ' μγ hT (by rw [cent_eq hgen hr hu y, ← hγu]) hμγ hinv hmap'.symm (fun g => φ (twConj (sigmaGL σ) g (incl (y * u * y⁻¹)))) (hφ.1.continuous.comp (by unfold t …`. Rewrite `hs` using `[Subgroup.mem_centralizer_singleton_iff]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Use the proof step `(fun g _ => ⟨g, 1, one_mem _, by simp⟩)`.

Use the proof step `⟨D', hD', fun x hx => by`. Take `⟨t, ht, d, hd, e⟩` from `hDs' x (by rw [twConj, a2]; exact subset_tsupport _ hx)`. Use `⟨t, ?_, d, hd, e⟩` and prove the remaining obligations. Rewrite `ht` using `[mem_twCent, a2]`. Rewrite using `[Subgroup.mem_centralizer_singleton_iff]`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 2`. Use function extensionality and compare the values at `x`. Use `set w := (y⁻¹ * x)⁻¹ * u * (y⁻¹ * x) with hwdef`. Establish `e : ∀ κ, twConj (sigmaGL σ) (incl x * κ) (incl (y * u * y⁻¹)) = κ⁻¹ * incl w * sigmaGL σ κ` using `fun κ => by`.

Simplify using `only [hwdef, twConj, map_mul, map_inv, sigma_incl, mul_inv_rev, inv_inv, mul_assoc]`. Establish `e' : x⁻¹ * γ * x = w ^ Module.finrank k E`. Use `conj_pow (a := (y⁻¹ * x)⁻¹) (b := u) (i := Module.finrank k E)` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Rewrite using `[hwdef, this, hγu]`.

Use `group`. Establish `e'' : ∀ κ, ((MonoidHom.id _) x * κ)⁻¹ * γ * ((MonoidHom.id _) x * κ) = κ⁻¹ * w ^ Module.finrank k E * κ` using `fun κ => by`. Rewrite using `[← e', MonoidHom.id_apply]`. Use `group`. Simplify using `only [e, e'']`.

Distinguish the cases in `hw : (incl w : GL (Fin n) E) ∈ K`. Conclude with `(h1 w hw).symm`. Rewrite using `[setIntegral_eq_zero_of_forall_eq_zero, setIntegral_eq_zero_of_forall_eq_zero]`. Introduce `κ hκ`. Assume the negation of the conclusion as `h0`.

Take `⟨u', hu', e2⟩` from `h2 _ h0`. Establish `e3` using `root_conj hr hu (mem.1 hu') (y := y⁻¹ * x * κ) (by rw [← e2, ← e', hγu]; group)`. Establish `e4 : w = κ * u' * κ⁻¹` using `by rw [← e3, hwdef]; group`. Rewrite `hw` using `[e4, map_mul, map_mul, map_inv]`. Conclude with `hw (K.mul_mem (K.mul_mem hκ hu') (K.inv_mem hκ))`.

Introduce `κ hκ`. Assume the negation of the conclusion as `h0`. Take `⟨κ', hκ', u', hu', e2⟩` from `hs _ h0`. Establish `s1 : sigmaGL σ κ ∈ K` using `mem.2 ((sg_mem_ball_iff hc.isom).mpr (mem.1 hκ))`. Establish `s2 : sigmaGL σ κ' ∈ K` using `mem.2 ((sg_mem_ball_iff hc.isom).mpr (mem.1 hκ'))`.

Establish `h5` using `K.mul_mem (K.mul_mem hκ (K.mul_mem (K.mul_mem (K.inv_mem hκ') hu') s2)) (K.inv_mem s1)`. Rewrite `h5` using `[← e2, show κ * (κ⁻¹ * incl w * sigmaGL σ κ) * (sigmaGL σ κ)⁻¹ = incl w by group]`. Conclude with `hw h5`. Introduce `x hx`. Take `⟨κ, hκ, u', hu', e⟩` from `hs _ hx`.

Take `⟨z, hz⟩` from `rigid hgen hr hu (mem.1 hu') (y := y) (y' := 1) (g := x * κ⁻¹) (by`. Rewrite using `[one_mul, inv_one, mul_one, map_mul (sigmaGL σ), map_inv]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨z, κ, hκ, by rw [hz]; group⟩`.
-/
theorem UpperTheory.ConvolutionTheory.Loc.nearCore :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
        (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)), μE.IsHaarMeasure → μk.IsHaarMeasure →
      ∀ r : ValueGroupWithZero E, r < valuation E (Module.finrank k E : E) →
      ∀ K : Subgroup (GL (Fin n) E), (K : Set (GL (Fin n) E)) = ball n r → IsOpen (K : Set (GL (Fin n) E)) → IsCompact (K : Set (GL (Fin n) E)) →
      ∀ φ ∈ SB (GL (Fin n) E), ∀ f ∈ SB (GL (Fin n) k),
        (∀ g, φ g ≠ 0 → ∃ κ ∈ K, ∃ u : GL (Fin n) k, incl u ∈ K ∧ g = κ⁻¹ * incl u * sigmaGL σ κ) →
        (∀ g, f g ≠ 0 → ∃ u : GL (Fin n) k, incl u ∈ K ∧ g = u ^ Module.finrank k E) →
        (∀ u : GL (Fin n) k, incl u ∈ K →
          ∫ κ in (K.comap (incl : GL (Fin n) k →* GL (Fin n) E) : Set (GL (Fin n) k)), f (κ⁻¹ * u ^ Module.finrank k E * κ) ∂μk =
            ∫ κ in (K : Set (GL (Fin n) E)), φ (κ⁻¹ * incl u * sigmaGL σ κ) ∂μE) →
        Match σ μE μk φ f := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n _ _ _ _ μE μk hμE hμk r hr K hK hKo hKc φ hφ f hf hs h2 h1
  obtain ⟨hc, -, hb⟩ := bridge k E σ
  have hj := (hb n).2.2.2.1
  obtain ⟨_, _, _, -⟩ := gLTop E n
  obtain ⟨_, _, _, -⟩ := gLTop k n
  have hθ : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) := ((extCont k E).2.2 n).2 σ
  have mem : ∀ {g : GL (Fin n) E}, g ∈ K ↔ g ∈ ball n r := fun {g} => by rw [← hK]; rfl
  refine ⟨fun δ γ h μδ μγ hδ hN hμδ hμγ hmap => ?_, fun γ μγ _ hno _ => ?_⟩
  swap
  · refine quot_zero _ _ _ fun y => ?_
    by_contra h0
    obtain ⟨u, -, hu⟩ := h2 _ h0
    exact hno ⟨incl u, (incl y)⁻¹, by rw [norm_incl, ← hu, map_mul, map_mul, map_inv, inv_inv]⟩
  have hγE : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
    rw [← sep_conj _ h, ← hN]
    exact hδ
  have hγ : IsRegSemisimple γ := (sep_incl γ).mp hγE
  by_cases hex : ∃ u y : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r ∧ γ = y * u ^ Module.finrank k E * y⁻¹
  swap
  · rw [twOrbIntegralC, orbIntegralC, quot_zero, quot_zero]
    · intro y
      by_contra h0
      obtain ⟨u, hu, e⟩ := h2 _ h0
      exact hex ⟨u, y, mem.1 hu, by rw [← e]; group⟩
    · intro g
      by_contra h0
      obtain ⟨κ, -, u, hu, e⟩ := hs _ h0
      replace hu := mem.1 hu
      have e1 := congrArg (twNorm (sigmaGL σ) (Module.finrank k E)) e
      rw [← twConj, twNorm_twConj_of_pow_eq_one _ (theta_pow σ), twNorm_twConj_of_pow_eq_one _ (theta_pow σ),
        ← normGL, ← normGL, hN, norm_incl] at e1
      obtain ⟨y, hy⟩ := conjDesc k E n γ (u ^ Module.finrank k E) hγ ⟨κ * g⁻¹ * h, by
        calc _ = κ * (κ⁻¹ * incl (u ^ Module.finrank k E) * κ) * κ⁻¹ := by group
          _ = _ := by rw [← e1]; group⟩
      exact hex ⟨u, y⁻¹, hu, by rw [hy]; group⟩
  obtain ⟨u, y, hu, hγu⟩ := hex
  have hN1 : normGL σ (incl (y * u * y⁻¹) : GL (Fin n) E) = incl γ := by rw [norm_incl, conj_pow, hγu]
  obtain ⟨g, hg⟩ := normInj k E σ hgen n γ hγ δ (incl (y * u * y⁻¹)) ⟨h, hN⟩ ⟨1, by simpa using hN1⟩
  obtain ⟨μ', hμ', hmap'⟩ := haarConj (GL (Fin n) E) _ _ g (mem_twCent_conj (sigmaGL σ) δ g) μδ hμδ
  rw [← twOrbConj k E σ n μE hμE δ g μδ μ' hδ hμδ hμ' hmap' φ hφ]
  have hz : h⁻¹ * g * incl γ = incl γ * (h⁻¹ * g) := by
    have e := hN1
    rw [hg, normGL, twNorm_twConj_of_pow_eq_one _ (theta_pow σ), ← normGL, hN] at e
    calc _ = h⁻¹ * g * (g⁻¹ * (h * incl γ * h⁻¹) * g) := by rw [e]
      _ = _ := by group
  have hpt : (fun x : twCent (sigmaGL σ) δ => g⁻¹ * (x : GL (Fin n) E) * g) =
      fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h := by
    funext x
    have e := comm_of_sep hγE (Subgroup.mem_centralizer_singleton_iff.mp
      (conj_twCent_mem_centralizer _ (theta_pow σ) hN x.2)) hz
    calc _ = (h⁻¹ * g)⁻¹ * (h⁻¹ * (x : GL (Fin n) E) * h * (h⁻¹ * g)) := by group
      _ = _ := by rw [e]; group
  rw [hpt, hmap] at hmap'
  clear hμ' hpt
  revert μ'
  rw [← hg]
  intro μ' hmap'
  have hT : IsClosed (Subgroup.centralizer ({γ} : Set (GL (Fin n) k)) : Set (GL (Fin n) k)) := by
    have e : (Subgroup.centralizer ({γ} : Set (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x} :=
      Set.ext fun x => Subgroup.mem_centralizer_singleton_iff
    rw [e]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hinv := (haarComm (GL (Fin n) k) _ hT (fun a ha b hb => comm_of_sep hγ
    (Subgroup.mem_centralizer_singleton_iff.mp ha) (Subgroup.mem_centralizer_singleton_iff.mp hb)) μγ hμγ).2.1
  have hreg : IsTwRegSemisimple σ (incl (y * u * y⁻¹) : GL (Fin n) E) := by
    rw [IsTwRegSemisimple, hN1]
    exact hγE
  obtain ⟨D, hD, hDs⟩ := orbProper k E σ hgen n _ hreg _ hφ.2
  haveI : ValuativeExtension k k := ⟨fun _ _ => Iff.rfl⟩
  obtain ⟨a1, a2, a3, -⟩ := untwist k n μk γ
  obtain ⟨D', hD', hDs'⟩ := orbProper k k 1 a1 n γ (a3 hγ) _ hf.2
  have hKo' : IsOpen ((K.comap (incl : GL (Fin n) k →* GL (Fin n) E) : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) :=
    hKo.preimage hj.continuous
  have hKc' : IsCompact ((K.comap (incl : GL (Fin n) k →* GL (Fin n) E) : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) :=
    hj.isCompact_preimage hKc
  rw [twOrbIntegralC, quotDesc _ _ incl hj μE μk hμE (unimod gLTop E n μE hμE).1 hμk (unimod gLTop k n μk hμk).1 K hKo hKc
    _ _ μ' μγ hT (by rw [cent_eq hgen hr hu y, ← hγu]) hμγ hinv hmap'.symm (fun g => φ (twConj (sigmaGL σ) g (incl (y * u * y⁻¹))))
    (hφ.1.continuous.comp (by unfold twConj; fun_prop))
    (fun s hs g => by rw [twConj_mul_left _ _ hs]) ?_ ⟨D, hD, fun x hx => hDs x (subset_tsupport _ hx)⟩, orbIntegralC,
    quotDesc _ _ (MonoidHom.id _) Topology.IsClosedEmbedding.id μk μk hμk (unimod gLTop k n μk hμk).1 hμk (unimod gLTop k n μk hμk).1
      _ hKo' hKc' _ _ μγ μγ hT (Subgroup.map_id _).symm hμγ hinv rfl (fun g => f (g⁻¹ * γ * g))
      (hf.1.continuous.comp (by fun_prop))
      (fun s hs g => by
        rw [Subgroup.mem_centralizer_singleton_iff] at hs
        congr 1
        calc _ = g⁻¹ * (s⁻¹ * (γ * s)) * g := by group
          _ = _ := by rw [← hs]; group)
      (fun g _ => ⟨g, 1, one_mem _, by simp⟩)
      ⟨D', hD', fun x hx => by
        obtain ⟨t, ht, d, hd, e⟩ := hDs' x (by rw [twConj, a2]; exact subset_tsupport _ hx)
        refine ⟨t, ?_, d, hd, e⟩
        rw [mem_twCent, a2] at ht
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc t * γ = t * (t⁻¹ * γ * t) := by rw [ht]
          _ = _ := by group⟩, Subgroup.comap_id]
  · congr 2
    funext x
    set w := (y⁻¹ * x)⁻¹ * u * (y⁻¹ * x) with hwdef
    have e : ∀ κ, twConj (sigmaGL σ) (incl x * κ) (incl (y * u * y⁻¹)) = κ⁻¹ * incl w * sigmaGL σ κ := fun κ => by
      simp only [hwdef, twConj, map_mul, map_inv, sigma_incl, mul_inv_rev, inv_inv, mul_assoc]
    have e' : x⁻¹ * γ * x = w ^ Module.finrank k E := by
      have := conj_pow (a := (y⁻¹ * x)⁻¹) (b := u) (i := Module.finrank k E)
      rw [inv_inv] at this
      rw [hwdef, this, hγu]
      group
    have e'' : ∀ κ, ((MonoidHom.id _) x * κ)⁻¹ * γ * ((MonoidHom.id _) x * κ) = κ⁻¹ * w ^ Module.finrank k E * κ := fun κ => by
      rw [← e', MonoidHom.id_apply]; group
    simp only [e, e'']
    by_cases hw : (incl w : GL (Fin n) E) ∈ K
    · exact (h1 w hw).symm
    · rw [setIntegral_eq_zero_of_forall_eq_zero, setIntegral_eq_zero_of_forall_eq_zero]
      · intro κ hκ
        by_contra h0
        obtain ⟨u', hu', e2⟩ := h2 _ h0
        have e3 := root_conj hr hu (mem.1 hu') (y := y⁻¹ * x * κ) (by rw [← e2, ← e', hγu]; group)
        have e4 : w = κ * u' * κ⁻¹ := by rw [← e3, hwdef]; group
        rw [e4, map_mul, map_mul, map_inv] at hw
        exact hw (K.mul_mem (K.mul_mem hκ hu') (K.inv_mem hκ))
      · intro κ hκ
        by_contra h0
        obtain ⟨κ', hκ', u', hu', e2⟩ := hs _ h0
        have s1 : sigmaGL σ κ ∈ K := mem.2 ((sg_mem_ball_iff hc.isom).mpr (mem.1 hκ))
        have s2 : sigmaGL σ κ' ∈ K := mem.2 ((sg_mem_ball_iff hc.isom).mpr (mem.1 hκ'))
        have h5 := K.mul_mem (K.mul_mem hκ (K.mul_mem (K.mul_mem (K.inv_mem hκ') hu') s2)) (K.inv_mem s1)
        rw [← e2, show κ * (κ⁻¹ * incl w * sigmaGL σ κ) * (sigmaGL σ κ)⁻¹ = incl w by group] at h5
        exact hw h5
  · intro x hx
    obtain ⟨κ, hκ, u', hu', e⟩ := hs _ hx
    obtain ⟨z, hz⟩ := rigid hgen hr hu (mem.1 hu') (y := y) (y' := 1) (g := x * κ⁻¹) (by
      rw [one_mul, inv_one, mul_one, map_mul (sigmaGL σ), map_inv]
      calc _ = κ * twConj (sigmaGL σ) x (incl (y * u * y⁻¹)) * (sigmaGL σ κ)⁻¹ := by unfold twConj; group
        _ = _ := by rw [e]; group)
    exact ⟨z, κ, hκ, by rw [hz]; group⟩
