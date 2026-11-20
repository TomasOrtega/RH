import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermDimensionUniqueStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTieAsm
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FormalGroupLinearSecond
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Actp

open MvPolynomial in

/- English proof (translation)
Use `GermD.jet_hom_ext fun i => ?_` and prove the remaining obligations. Establish `hk : ∀ P ∈ orig R κ', (aeval (fun _ : κ' => (0 : R))) P = 0`. Introduce `P hP`. Establish `: orig R κ' ≤ RingHom.ker ((aeval (fun _ : κ' => (0 : R)) : MvPolynomial κ' R →ₐ[R] R) : MvPolynomial κ' R →+* R)`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨j, rfl⟩`. Simplify using `[RingHom.mem_ker]`. Conclude with `this hP`. Establish `e1 : (jetAug : Jet R κ' m →ₐ[R] R) ((jetMap φ hφ) (Ideal.Quotient.mk _ (X i))) = aeval (fun _ : κ' => (0 : R)) (φ i)`. Rewrite using `[GermD.jetMap_mk, aeval_X]`.

Both sides reduce to the same expression. Establish `e2 : (jetAug : Jet R κ m →ₐ[R] R) (Ideal.Quotient.mk _ (X i)) = 0` using `by show aeval (fun _ : κ => (0 : R)) (X i) = 0`. Simplify using the standard rewrite rules. Rewrite using `[AlgHom.comp_apply, e1, e2, hk _ (hφ i)]`.
-/
theorem aug_jetMap {R : Type} [CommRing R] {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' R)
    (hφ : ∀ i, φ i ∈ orig R κ') :
    (jetAug : Jet R κ' m →ₐ[R] R).comp (jetMap φ hφ) = jetAug := by
  refine GermD.jet_hom_ext fun i => ?_
  have hk : ∀ P ∈ orig R κ', (aeval (fun _ : κ' => (0 : R))) P = 0 := by
    intro P hP
    have : orig R κ' ≤ RingHom.ker ((aeval (fun _ : κ' => (0 : R)) : MvPolynomial κ' R →ₐ[R] R) : MvPolynomial κ' R →+* R) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      simp [RingHom.mem_ker]
    exact this hP
  have e1 : (jetAug : Jet R κ' m →ₐ[R] R) ((jetMap φ hφ) (Ideal.Quotient.mk _ (X i))) = aeval (fun _ : κ' => (0 : R)) (φ i) := by
    rw [GermD.jetMap_mk, aeval_X]; rfl
  have e2 : (jetAug : Jet R κ m →ₐ[R] R) (Ideal.Quotient.mk _ (X i)) = 0 := by
    show aeval (fun _ : κ => (0 : R)) (X i) = 0
    simp
  rw [AlgHom.comp_apply, e1, e2, hk _ (hφ i)]

/- English proof (translation)
The claim follows from `DFunLike.congr_fun (aug_jetMap (m := m) (fun i => φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i))) (fun _ => sub_const_mem_orig _)) z`.
-/
theorem aug_subst {R : Type} [CommRing R] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' R) (z : Jet R κ m) :
    (jetAug : Jet R κ' m →ₐ[R] R) (jetSubstP m φ z) = (jetAug : Jet R κ m →ₐ[R] R) z :=
  DFunLike.congr_fun (aug_jetMap (m := m) (fun i => φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i)))
    (fun _ => sub_const_mem_orig _)) z

/- English proof (translation)
Use `show MvPolynomial.aeval (fun _ : κ => (0 : R)) (MvPolynomial.X q) = 0`. Simplify using the standard rewrite rules.
-/
theorem aug_X {R : Type} [CommRing R] {κ : Type} (m : ℕ) (q : κ) :
    (jetAug : Jet R κ m →ₐ[R] R) (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : R)) (MvPolynomial.X q) = 0
  simp

/- English proof (translation)
Use `ext1`. Simplify using `only [homAt, spMap, Over.comp_left, Over.homMk_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Both sides reduce to the same expression.
-/
theorem homAt_comp {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {A B C : Type} [CommRing A] [Algebra S A]
    [CommRing B] [Algebra S B] [CommRing C] [Algebra S C] (f : A →ₐ[S] B) (g : B →ₐ[S] C) :
    homAt x0 (g.comp f) = homAt x0 g ≫ homAt x0 f := by
  ext1
  simp only [homAt, spMap, Over.comp_left, Over.homMk_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

section Val

open MvPolynomial

variable {k : Type} [Field k] {d : ℕ}

/- English proof (translation)
Establish `h : (fun q : Fin 1 × Fin d => (C (w q.2) * X () : MvPolynomial Unit k) - C (constantCoeff (C (w q.2) * X () : MvPolynomial Unit k))) = fun q => C (w q.2) * X ()`. Use function extensionality and compare the values at `q`. Simplify using the standard rewrite rules. Rewrite using `[CIndFrExp2.jetSubstP_mk, h]`.
-/
theorem subst_mk (w : Fin d → k) (p : ℕ) (P : MvPolynomial (Fin 1 × Fin d) k) :
    jetSubstP p (fun q : Fin 1 × Fin d => C (w q.2) * X ()) (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (aeval (fun q : Fin 1 × Fin d => (C (w q.2) * X () : MvPolynomial Unit k)) P) := by
  have h : (fun q : Fin 1 × Fin d => (C (w q.2) * X () : MvPolynomial Unit k) -
      C (constantCoeff (C (w q.2) * X () : MvPolynomial Unit k))) = fun q => C (w q.2) * X () := by
    funext q
    simp
  rw [CIndFrExp2.jetSubstP_mk, h]

def vW (w : Fin d → k) (B : Type) [CommRing B] [Algebra k B] (p : ℕ) : Fin 1 × Fin d → Jet B Unit p :=
  fun q => algebraMap k _ (w q.2) * dQ B p

/- English proof (translation)
Establish `h1 : ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) : MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) P ∈ Ideal.map ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) : MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) (orig k (Fin 1 …` using `Ideal.mem_map_of_mem _ hP`. Rewrite `h1` using `[map_orig_pow]`. Establish `h2 : Ideal.span (Set.range fun i => ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) : MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) (X i)) ≤ Ideal.span {dQ B p}`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`.

Establish `: ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) : MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) (X q) = vW w B p q` using `by simp`. Use `beta_reduce`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)`. Establish `h3` using `Ideal.pow_right_mono h2 (p + 1) h1`.

Rewrite `h3` using `[dQ_span_pow]`. Conclude with `(Submodule.mem_bot _).1 h3`.
-/
theorem aeval_vW_orig (w : Fin d → k) (B : Type) [CommRing B] [Algebra k B] (p : ℕ)
    (P : MvPolynomial (Fin 1 × Fin d) k) (hP : P ∈ orig k (Fin 1 × Fin d) ^ (p + 1)) :
    aeval (vW w B p) P = 0 := by
  have h1 : ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) :
      MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) P ∈
      Ideal.map ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) :
        MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) (orig k (Fin 1 × Fin d) ^ (p + 1)) :=
    Ideal.mem_map_of_mem _ hP
  rw [map_orig_pow] at h1
  have h2 : Ideal.span (Set.range fun i =>
      ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) :
        MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) (X i)) ≤ Ideal.span {dQ B p} := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨q, rfl⟩
    have : ((aeval (vW w B p) : MvPolynomial (Fin 1 × Fin d) k →ₐ[k] Jet B Unit p) :
        MvPolynomial (Fin 1 × Fin d) k →+* Jet B Unit p) (X q) = vW w B p q := by simp
    beta_reduce
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have h3 := Ideal.pow_right_mono h2 (p + 1) h1
  rw [dQ_span_pow] at h3
  exact (Submodule.mem_bot _).1 h3

/- English proof (translation)
Rewrite using `[subst_mk]`. Establish `e : ∀ Q : MvPolynomial Unit k, inL (k` using `k) B p (Ideal.Quotient.mk _ Q) = aeval (fun _ => dQ B p) Q := fun _ => rfl`. Rewrite using `[e, ← AlgHom.comp_apply, comp_aeval]`. Establish `h : (fun q : Fin 1 × Fin d => (aeval (R` using `k) (fun _ : Unit => dQ B p)) (C (w q.2) * X () : MvPolynomial Unit k)) = vW w B p := by`. Use function extensionality and compare the values at `q`.

Simplify using `[vW]`. Conclude with `congrArg (fun u => aeval u P) h`.
-/
theorem inL_subst (w : Fin d → k) (B : Type) [CommRing B] [Algebra k B] (p : ℕ) (P : MvPolynomial (Fin 1 × Fin d) k) :
    inL (k := k) B p (jetSubstP p (fun q : Fin 1 × Fin d => C (w q.2) * X ()) (Ideal.Quotient.mk _ P)) =
      aeval (vW w B p) P := by
  rw [subst_mk]
  have e : ∀ Q : MvPolynomial Unit k, inL (k := k) B p (Ideal.Quotient.mk _ Q) = aeval (fun _ => dQ B p) Q := fun _ => rfl
  rw [e, ← AlgHom.comp_apply, comp_aeval]
  have h : (fun q : Fin 1 × Fin d => (aeval (R := k) (fun _ : Unit => dQ B p)) (C (w q.2) * X () : MvPolynomial Unit k)) =
      vW w B p := by
    funext q
    simp [vW]
  exact congrArg (fun u => aeval u P) h

/- English proof (translation)
Establish `e1 : jq w p m (Ideal.Quotient.mk _ (psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) f)) = aeval (vW w (Jet k (Fin 1 × Fin d) m) p) (psTrunc (p + m + 1) f)` using `by show aeval _ (rename _ (psTrunc (p + m + 1) f)) = _`. Rewrite using `[aeval_rename]`. Use `congrArg (fun u => aeval u (psTrunc (p + m + 1) f)) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Simplify using `[vW]`.

Rewrite using `[e1, inL_subst, ← sub_eq_zero, ← map_sub]`. Conclude with `aeval_vW_orig w _ p _ (CIndFrExp2.psTrunc_sub_mem f (by omega))`.
-/
theorem jq_first (w : Fin d → k) (p m : ℕ) (f : MvPowerSeries (Fin 1 × Fin d) k) :
    jq w p m (Ideal.Quotient.mk _ (psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) f)) =
      inL (k := k) (Jet k (Fin 1 × Fin d) m) p
        (jetSubstP p (fun q : Fin 1 × Fin d => C (w q.2) * X ()) (Ideal.Quotient.mk _ (psTrunc p f))) := by
  have e1 : jq w p m (Ideal.Quotient.mk _ (psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) f)) =
      aeval (vW w (Jet k (Fin 1 × Fin d) m) p) (psTrunc (p + m + 1) f) := by
    show aeval _ (rename _ (psTrunc (p + m + 1) f)) = _
    rw [aeval_rename]
    refine congrArg (fun u => aeval u (psTrunc (p + m + 1) f)) ?_
    funext q
    simp [vW]
  rw [e1, inL_subst, ← sub_eq_zero, ← map_sub]
  exact aeval_vW_orig w _ p _ (CIndFrExp2.psTrunc_sub_mem f (by omega))

end Val

end GlobalTheory.CompanionTheory.Ar.Coc.Actp

namespace GlobalTheory.CompanionTheory.Ar.Coc

open MvPolynomial in

/- English proof (translation)
Take `⟨ψ, hψ⟩ : ∃ ψ : Jet k (Fin 1 × Fin d) p →ₐ[k] Jet k (Fin 1 × Fin d) p, ψ = jetSubstP p fun q : Fin 1 × Fin d => psTrunc p (g.B.A.act (p : 𝓞 E) q.2)` from `⟨_, rfl⟩`. Take `⟨χ₀, hχ₀⟩ : ∃ χ₀ : Jet k (Fin 1 × Fin d) p →ₐ[k] Jet k Unit p, χ₀ = (Algebra.ofId k (Jet k Unit p)).comp (jetAug : Jet k (Fin 1 × Fin d) p →ₐ[k] k)` from `⟨_, rfl⟩`. Establish `e : g.x p ≫ t.act.act (p : 𝓞 E) = homAt x ψ ≫ g.x p`. Rewrite using `[hψ]`. Conclude with `g.chart.act p (p : 𝓞 E)`.

Establish `h1 : homAt x (σ.comp ψ) ≫ g.x p = 1`. Rewrite using `[Actp.homAt_comp, Category.assoc, ← e, ← Category.assoc, PullbackSections.act_natCast, MonObj.comp_pow, Category.comp_id]`. Conclude with `hy`. Establish `h0 : homAt x χ₀ ≫ g.x p = 1`. Rewrite using `[hχ₀, Actp.homAt_comp, Category.assoc, g.chart.zero p, MonObj.comp_one]`.

Establish `a1 : ∀ z, (jetAug : Jet k Unit p →ₐ[k] k) (σ (ψ z)) = (jetAug : Jet k (Fin 1 × Fin d) p →ₐ[k] k) z`. Introduce `z`. Rewrite using `[hσ, hψ, Actp.aug_subst]`. Take `⟨χ, -, huniq⟩` from `(GlobalTheory.T.formal_germ_dimension_unique E H hst X0 t k x d g).2 Unit p 1 (MonObj.comp_one _)`. Establish `c1` using `huniq (σ.comp ψ) ⟨fun q => by rw [AlgHom.comp_apply, a1, Actp.aug_X], h1.symm⟩`.

Establish `c0` using `huniq χ₀ ⟨fun q => by`. Simplify using `only [hχ₀, AlgHom.comp_apply, Actp.aug_X, map_zero], h0.symm⟩`. Establish `c : σ.comp ψ = χ₀` using `c1.trans c0.symm`. Establish `hc : MvPowerSeries.constantCoeff (g.B.A.act (p : 𝓞 E) j) = 0` using `g.B.A.const _ _`. Establish `cc : constantCoeff (psTrunc p (g.B.A.act (p : 𝓞 E) j)) = 0`.

Establish `h` using `GermFun.coeff_psTrunc p (g.B.A.act (p : 𝓞 E) j) 0 (by simp)`. Rewrite using `[MvPolynomial.constantCoeff_eq, h]`. Simplify using `using hc`. Establish `e' : ψ (Ideal.Quotient.mk _ (X ((0 : Fin 1), j))) = Ideal.Quotient.mk _ (psTrunc p (g.B.A.act (p : 𝓞 E) j))`. Rewrite using `[hψ, CIndFrExp2.jetSubstP_mk, aeval_X, cc, map_zero, sub_zero]`.

Establish `e2` using `DFunLike.congr_fun c (Ideal.Quotient.mk _ (X ((0 : Fin 1), j)))`. Rewrite `e2` using `[AlgHom.comp_apply, e', hχ₀, AlgHom.comp_apply, Actp.aug_X, map_zero]`. Conclude with `e2`.
-/
theorem actp_at_point {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)]
    (hst : ∀ a : 𝓞 E, star a = H.bar a) {X0 : Scheme.{0}} (t : SAB H X0) {k : Type} [Field k] (p : ℕ)
    (x : Sp k ⟶ X0) {d : ℕ} (g : GermAt t x d)
    (σ : Jet k (Fin 1 × Fin d) p →ₐ[k] Jet k Unit p)
    (hσ : ∀ z, (jetAug : Jet k Unit p →ₐ[k] k) (σ z) = (jetAug : Jet k (Fin 1 × Fin d) p →ₐ[k] k) z)
    (hy : (homAt x σ ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) ^ p = 1) (j : Fin d) :
    σ (Ideal.Quotient.mk _ (psTrunc p (g.B.A.act (p : 𝓞 E) j))) = 0 := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Jet k (Fin 1 × Fin d) p →ₐ[k] Jet k (Fin 1 × Fin d) p,
      ψ = jetSubstP p fun q : Fin 1 × Fin d => psTrunc p (g.B.A.act (p : 𝓞 E) q.2) := ⟨_, rfl⟩
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀ : Jet k (Fin 1 × Fin d) p →ₐ[k] Jet k Unit p,
      χ₀ = (Algebra.ofId k (Jet k Unit p)).comp (jetAug : Jet k (Fin 1 × Fin d) p →ₐ[k] k) := ⟨_, rfl⟩
  have e : g.x p ≫ t.act.act (p : 𝓞 E) = homAt x ψ ≫ g.x p := by
    rw [hψ]; exact g.chart.act p (p : 𝓞 E)
  have h1 : homAt x (σ.comp ψ) ≫ g.x p = 1 := by
    rw [Actp.homAt_comp, Category.assoc, ← e, ← Category.assoc,
      PullbackSections.act_natCast, MonObj.comp_pow, Category.comp_id]
    exact hy
  have h0 : homAt x χ₀ ≫ g.x p = 1 := by
    rw [hχ₀, Actp.homAt_comp, Category.assoc, g.chart.zero p, MonObj.comp_one]
  have a1 : ∀ z, (jetAug : Jet k Unit p →ₐ[k] k) (σ (ψ z)) = (jetAug : Jet k (Fin 1 × Fin d) p →ₐ[k] k) z := by
    intro z
    rw [hσ, hψ, Actp.aug_subst]
  obtain ⟨χ, -, huniq⟩ := (GlobalTheory.T.formal_germ_dimension_unique E H hst X0 t k x d g).2 Unit p 1 (MonObj.comp_one _)
  have c1 := huniq (σ.comp ψ) ⟨fun q => by rw [AlgHom.comp_apply, a1, Actp.aug_X], h1.symm⟩
  have c0 := huniq χ₀ ⟨fun q => by
    simp only [hχ₀, AlgHom.comp_apply, Actp.aug_X, map_zero], h0.symm⟩
  have c : σ.comp ψ = χ₀ := c1.trans c0.symm
  have hc : MvPowerSeries.constantCoeff (g.B.A.act (p : 𝓞 E) j) = 0 := g.B.A.const _ _
  have cc : constantCoeff (psTrunc p (g.B.A.act (p : 𝓞 E) j)) = 0 := by
    have h := GermFun.coeff_psTrunc p (g.B.A.act (p : 𝓞 E) j) 0 (by simp)
    rw [MvPolynomial.constantCoeff_eq, h]
    simpa using hc
  have e' : ψ (Ideal.Quotient.mk _ (X ((0 : Fin 1), j))) = Ideal.Quotient.mk _ (psTrunc p (g.B.A.act (p : 𝓞 E) j)) := by
    rw [hψ, CIndFrExp2.jetSubstP_mk, aeval_X, cc, map_zero, sub_zero]
  have e2 := DFunLike.congr_fun c (Ideal.Quotient.mk _ (X ((0 : Fin 1), j)))
  rw [AlgHom.comp_apply, e', hχ₀, AlgHom.comp_apply, Actp.aug_X, map_zero] at e2
  exact e2

/- English proof (translation)
Introduce `E _ _ _ H _ hst X0 t k _ p _ _ x d g w m hy j`. Rewrite using `[Actp.jq_first, actp_at_point H hst t p x g _ (fun z => Actp.aug_subst p _ z) hy j, map_zero]`.
-/
theorem actp_vanish : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ), (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) ^ p = 1 → ∀ j, jq w p m (Ideal.Quotient.mk _ (psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j))) = 0 := by
  intro E _ _ _ H _ hst X0 t k _ p _ _ x d g w m hy j
  rw [Actp.jq_first, actp_at_point H hst t p x g _ (fun z => Actp.aug_subst p _ z) hy j, map_zero]

end GlobalTheory.CompanionTheory.Ar.Coc
