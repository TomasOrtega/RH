import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.RapidBound
import Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.ActsOfReads
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsFull
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfSurj

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

open PositivityTheory.ThKEst PositivityTheory.KCo
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Take `⟨fr, hg, -, -, -, C, k, hC⟩` from `hS F E σ hB.cm n _ (hE F E σ B hB n X _ _ (Or.inl hX)).1`. Establish `hr : 0 < fr.r` using `Nat.pos_of_ne_zero fun h0 => by`. Take `⟨Y', Y₁, H, -, -, hA⟩` from `hH F E σ B hB n (n - 2) (by omega) (by omega) X r s h1 h2 hX 0 1 one_pos (by omega)`.

Use `hA.xy` as an intermediate fact. Rewrite `this` using `[hg.aniso H.x (fun i => absurd i.2 (by omega)) hA.xx]`. Simplify using `[form] at this`. Set `A` to `max C 0 * (b + 1) ^ k`. Establish `ht' : (fun _ => |A|) ∈ Cone fr.r` using `⟨antitone_const, fun _ => abs_nonneg _⟩`.

Establish `b0 : 0 ≤ b` using `(NNReal.coe_nonneg _).trans (hn 1)`. Take `⟨γ, hγ⟩` from `exists_lt_of_ciInf_lt (f := fun γ : ratU σ X.J => ht (γ.1 * fr.a fun _ => |A|)) (a := qht (fr.a fun _ => |A|) + 1) (lt_add_one _)`. Establish `e1 : (ht (γ.1 * fr.a fun _ => |A|) : ℝ) ≤ b + 1`. Use `hn (fr.a fun _ => |A|)` as an intermediate fact. Establish `h' : (ht (γ.1 * fr.a fun _ => |A|) : ℝ) < qht (fr.a fun _ => |A|) + 1` using `by exact_mod_cast hγ`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e2 : Real.exp (∑ _i : Fin fr.r, |A|) ≤ A` using `((hC _ ht').2 γ γ.2).trans (by`. Simplify using `only [A]`. Use `gcongr`. Conclude with `le_max_left _ _)`.

Establish `e3 : |A| ≤ ∑ _i : Fin fr.r, |A|` using `Finset.single_le_sum (fun _ _ => abs_nonneg A) (Finset.mem_univ ⟨0, hr⟩)`. Combine the linear relations using `[Real.add_one_le_exp (∑ _i : Fin fr.r, |A|), le_abs_self A]`.
-/
theorem qht_unbdd (hE : EpsOf) (hS : SiegelAll) (hH : PositivityTheory.ThKG.Tow.PlaneHerm) (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    (h1 : 1 ≤ r) (h2 : 1 ≤ s) (h3 : 3 ≤ n) (b : ℝ) : ∃ g : UA σ X.J, b < qht g := by
  by_contra hn
  push Not at hn
  obtain ⟨fr, hg, -, -, -, C, k, hC⟩ := hS F E σ hB.cm n _ (hE F E σ B hB n X _ _ (Or.inl hX)).1
  have hr : 0 < fr.r := Nat.pos_of_ne_zero fun h0 => by
    obtain ⟨Y', Y₁, H, -, -, hA⟩ := hH F E σ B hB n (n - 2) (by omega) (by omega) X r s h1 h2 hX 0 1 one_pos (by omega)
    have := hA.xy
    rw [hg.aniso H.x (fun i => absurd i.2 (by omega)) hA.xx] at this
    simp [form] at this
  let A := max C 0 * (b + 1) ^ k
  have ht' : (fun _ => |A|) ∈ Cone fr.r := ⟨antitone_const, fun _ => abs_nonneg _⟩
  have b0 : 0 ≤ b := (NNReal.coe_nonneg _).trans (hn 1)
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (f := fun γ : ratU σ X.J => ht (γ.1 * fr.a fun _ => |A|))
    (a := qht (fr.a fun _ => |A|) + 1) (lt_add_one _)
  have e1 : (ht (γ.1 * fr.a fun _ => |A|) : ℝ) ≤ b + 1 := by
    have := hn (fr.a fun _ => |A|)
    have h' : (ht (γ.1 * fr.a fun _ => |A|) : ℝ) < qht (fr.a fun _ => |A|) + 1 := by exact_mod_cast hγ
    linarith
  have e2 : Real.exp (∑ _i : Fin fr.r, |A|) ≤ A := ((hC _ ht').2 γ γ.2).trans (by
    simp only [A]
    gcongr
    exact le_max_left _ _)
  have e3 : |A| ≤ ∑ _i : Fin fr.r, |A| := Finset.single_le_sum (fun _ _ => abs_nonneg A) (Finset.mem_univ ⟨0, hr⟩)
  linarith [Real.add_one_le_exp (∑ _i : Fin fr.r, |A|), le_abs_self A]

/- English proof (translation)
Simplify using `only [th, pet, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]`.
-/
theorem th_left (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)) (f) (Ψ : Fn F n d) (g u : UA σ X.J) :
    th om μ D f (om (u, 1) Ψ) g = th om μ D f Ψ (g * u) := by
  simp only [th, pet, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

/- English proof (translation)
Simplify using `only [th, pet, theta_add hp hΦ hΨ, star_add, mul_add]`. Conclude with `integral_add (th_int hB hE hV hp hμ hD hf hΦ g) (th_int hB hE hV hp hμ hD hf hΨ g)`.
-/
theorem th_add (hB : ThetaBasic) (hE : EpsOf) (hV : FinVolU) (hp : IsPair B M χX χW om r s r' s') {μ : Measure (UA σ W.J)}
    {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ) {f} (hf : IsRapid (Y := W) f) {Φ Ψ}
    (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _) (g) : th om μ D f (Φ + Ψ) g = th om μ D f Φ g + th om μ D f Ψ g := by
  simp only [th, pet, theta_add hp hΦ hΨ, star_add, mul_add]
  exact integral_add (th_int hB hE hV hp hμ hD hf hΦ g) (th_int hB hE hV hp hμ hD hf hΨ g)

/- English proof (translation)
Simplify using `only [th, pet, theta_smul hp c hΨ, star_mul', ← integral_const_mul, mul_left_comm]`.
-/
theorem th_smul (hp : IsPair B M χX χW om r s r' s') (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)) (f) (c : ℂ) {Ψ}
    (hΨ : Ψ ∈ schA F _) (g) : th om μ D f (c • Ψ) g = star c * th om μ D f Ψ g := by
  simp only [th, pet, theta_smul hp c hΨ, star_mul', ← integral_const_mul, mul_left_comm]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp h1 h2 h3 h4 hν μ D hμ hD f hf hc`. Use `haveI := finW hE hV hp hμ hD`. Establish `so : ∀ Ψ ∈ M.So B.ψ B.τ₁, th om μ D f Ψ 1 = 0` using `fun Ψ hΨ => by`. Establish `s₁` using `(hF F E σ B n d X W M χX χW om r s r' s' hp).2.2.1 Ψ hΨ`. Take `⟨C, k, hC⟩` from `hSo F E σ B n d X W M χX χW om r s r' s' hp Ψ hΨ 1`.

Take `⟨K, -, hK⟩` from `rapid_bound hf k`. Assume the negation of the conclusion as `h0`. Establish `p0` using `norm_pos_iff.2 h0`. Take `⟨g, hg⟩` from `qht_unbdd hE hS hH hp.base hp.herm h1 h2 h3 (max C 0 * K * (μ.restrict D).real Set.univ / ‖th om μ D f Ψ 1‖)`. Rewrite `hg` using `[div_lt_iff₀' p0, ← hc Ψ s₁ g]`.

Use `hg.not_ge ?_` and prove the remaining obligations. Establish `: ‖∫ h in D, f h * star (theta om Ψ g h) * ((qht g : ℝ) : ℂ) ∂μ‖ ≤ max C 0 * K * (μ.restrict D).real Set.univ` using `norm_integral_le_of_norm_le_const (.of_forall fun h => by`. Rewrite using `[norm_mul, norm_mul, norm_star, mul_assoc, Complex.norm_real, NNReal.norm_eq]`. Conclude with `hK (fun h => ‖theta om Ψ g h‖ * qht g) C (fun γ hγ h => by simp only [theta_rat hB hp s₁ g γ hγ]) (fun h => by simpa using hC g h) h)`. Rewrite `this` using `[integral_mul_const, norm_mul, Complex.norm_real, NNReal.norm_eq]`. Then use the resulting hypothesis.

Set `K : Submodule ℂ (Fn F n d)` to `{ carrier := {Ψ | Ψ ∈ schA F _ ∧ th om μ D f Ψ 1 = 0} add_mem' := fun a b => ⟨add_mem a.1 b.1, by rw [th_add hB hE hV hp hμ hD hf a.1 b.1, a.2, b.2, add_zero]⟩ zero_mem' := ⟨zero_mem _, so 0 (zero_mem _)⟩ smul_mem' := fun c _ a => ⟨Submodule.smul_mem _ c a.1, by rw [th_smul hp μ …`. Use `fun Ψ hΨ g => (hc Ψ hΨ g).trans (schA_le K (fun f₀ φ p1 p2 => ?_) hΨ).2` and prove the remaining obligations. Take `⟨⟨ι, hι⟩, ν, α, u1, -, n1, hd⟩` from `hDi F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.good hp.weil hp.hX hp.hW B.v₁ B.τ₁`. Take `⟨φ₀, s₀, f0, a0⟩` from `exists_full surjectivity_statement hι.bij (hd ι hι) u1 (fun e => (n1 (by omega) h4 e).elim (hν _) (hν _)) (p1 B.v₁)`. Take `⟨T, t1, t2, t3⟩` from `intersection_update_fsHerm_neg_one B.v₁ f₀ p1 p2`.

Establish `k1 : augAt om B.v₁ ≤ K.comap T` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨u, -, ψ, hψ, ψ₁, hψ₁, hA, rfl⟩`. Use `⟨t2 _ (sub_mem hψ₁ hψ), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_add_neg, ← neg_one_smul ℂ (T ψ), th_add hB hE hV hp hμ hD hf (t2 _ hψ₁) (Submodule.smul_mem _ _ (t2 _ hψ)), th_smul hp μ D f _ (t2 _ hψ), ← t3 _ _ hψ _ hA, th_left, hc _ (t2 _ hψ)]`. Use the proof step `simp)`.

Establish `k2 : T φ₀ ∈ K` using `⟨t2 _ s₀, so _ (Submodule.subset_span ⟨f₀, _, fun w => by`. Distinguish the cases in `hw : w = B.v₁`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self]` and apply the resulting hypothesis. Rewrite using `[Function.update_of_ne hw]; exact p1 w, by filter_upwards [p2, hp.good.std, eventually_cofinite_ne B.v₁] with w h h' hw using (Function.update_of_ne hw _ _).trans (h.trans h'.symm), by`.

Rewrite using `[Function.update_self]`. Conclude with `⟨s₀, ι, hι, f0.2⟩, t1 φ₀⟩)⟩`. Use `add_mem (k1 a0) k2` as an intermediate fact. Rewrite `this` using `[Submodule.mem_comap, sub_add_cancel, t1, Function.update_eq_self]`. Then use the resulting hypothesis.
-/
theorem thZero_of (hB : ThetaBasic) (hE : EpsOf) (hV : FinVolU) (hS : SiegelAll) (hSo : SoDecay) (hF : SoFin)
    (hH : PositivityTheory.ThKG.Tow.PlaneHerm) (hDi : DictSt) : ThZero := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp h1 h2 h3 h4 hν μ D hμ hD f hf hc
  haveI := finW hE hV hp hμ hD
  have so : ∀ Ψ ∈ M.So B.ψ B.τ₁, th om μ D f Ψ 1 = 0 := fun Ψ hΨ => by
    have s₁ := (hF F E σ B n d X W M χX χW om r s r' s' hp).2.2.1 Ψ hΨ
    obtain ⟨C, k, hC⟩ := hSo F E σ B n d X W M χX χW om r s r' s' hp Ψ hΨ 1
    obtain ⟨K, -, hK⟩ := rapid_bound hf k
    by_contra h0
    have p0 := norm_pos_iff.2 h0
    obtain ⟨g, hg⟩ := qht_unbdd hE hS hH hp.base hp.herm h1 h2 h3 (max C 0 * K * (μ.restrict D).real Set.univ / ‖th om μ D f Ψ 1‖)
    rw [div_lt_iff₀' p0, ← hc Ψ s₁ g] at hg
    refine hg.not_ge ?_
    have : ‖∫ h in D, f h * star (theta om Ψ g h) * ((qht g : ℝ) : ℂ) ∂μ‖ ≤ max C 0 * K * (μ.restrict D).real Set.univ :=
      norm_integral_le_of_norm_le_const (.of_forall fun h => by
        rw [norm_mul, norm_mul, norm_star, mul_assoc, Complex.norm_real, NNReal.norm_eq]
        exact hK (fun h => ‖theta om Ψ g h‖ * qht g) C (fun γ hγ h => by simp only [theta_rat hB hp s₁ g γ hγ])
          (fun h => by simpa using hC g h) h)
    rwa [integral_mul_const, norm_mul, Complex.norm_real, NNReal.norm_eq] at this
  let K : Submodule ℂ (Fn F n d) :=
    { carrier := {Ψ | Ψ ∈ schA F _ ∧ th om μ D f Ψ 1 = 0}
      add_mem' := fun a b => ⟨add_mem a.1 b.1, by rw [th_add hB hE hV hp hμ hD hf a.1 b.1, a.2, b.2, add_zero]⟩
      zero_mem' := ⟨zero_mem _, so 0 (zero_mem _)⟩
      smul_mem' := fun c _ a => ⟨Submodule.smul_mem _ c a.1, by rw [th_smul hp μ D f c a.1, a.2, mul_zero]⟩ }
  refine fun Ψ hΨ g => (hc Ψ hΨ g).trans (schA_le K (fun f₀ φ p1 p2 => ?_) hΨ).2
  obtain ⟨⟨ι, hι⟩, ν, α, u1, -, n1, hd⟩ := hDi F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.good hp.weil
    hp.hX hp.hW B.v₁ B.τ₁
  obtain ⟨φ₀, s₀, f0, a0⟩ := exists_full surjectivity_statement hι.bij (hd ι hι) u1
    (fun e => (n1 (by omega) h4 e).elim (hν _) (hν _)) (p1 B.v₁)
  obtain ⟨T, t1, t2, t3⟩ := intersection_update_fsHerm_neg_one B.v₁ f₀ p1 p2
  have k1 : augAt om B.v₁ ≤ K.comap T := Submodule.span_le.2 (by
    rintro _ ⟨u, -, ψ, hψ, ψ₁, hψ₁, hA, rfl⟩
    refine ⟨t2 _ (sub_mem hψ₁ hψ), ?_⟩
    rw [map_sub, sub_eq_add_neg, ← neg_one_smul ℂ (T ψ), th_add hB hE hV hp hμ hD hf (t2 _ hψ₁) (Submodule.smul_mem _ _ (t2 _ hψ)),
      th_smul hp μ D f _ (t2 _ hψ), ← t3 _ _ hψ _ hA, th_left, hc _ (t2 _ hψ)]
    simp)
  have k2 : T φ₀ ∈ K := ⟨t2 _ s₀, so _ (Submodule.subset_span ⟨f₀, _, fun w => by
    by_cases hw : w = B.v₁
    · subst hw; rwa [Function.update_self]
    · rw [Function.update_of_ne hw]; exact p1 w, by
      filter_upwards [p2, hp.good.std, eventually_cofinite_ne B.v₁] with w h h' hw using
        (Function.update_of_ne hw _ _).trans (h.trans h'.symm), by
      rw [Function.update_self]; exact ⟨s₀, ι, hι, f0.2⟩, t1 φ₀⟩)⟩
  have := add_mem (k1 a0) k2
  rwa [Submodule.mem_comap, sub_add_cancel, t1, Function.update_eq_self] at this

end PositivityTheory.ThKEnd.Orth

end
