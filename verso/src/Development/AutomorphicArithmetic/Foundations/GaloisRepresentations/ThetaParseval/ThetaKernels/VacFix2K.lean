import Development.WeilBound.ThetaLifts.LatticeBasics.PresDOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseBadStmt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LocConeVfEig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsBetaK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Vf2
open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locrep PositivityTheory.ThKG.Loc.Cone.Vf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {v : Pl F}
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM χ _ dd omd ⟨d', hd', hdd⟩ ⟨_, hsp, hrule⟩ K hK v hv g hk hg`. Establish `hL` using `hX.lat`. Establish `vd` using `hM.vac v`. Take `⟨hsb, h0, -⟩` from `hM.vac v`. Take `⟨r₀, x₀, h₀, h₁⟩` from `exists_base (Fin n × Fin d) v`.

Use `set Φ := tens (evFin F v) (M.vac v) r₀ with hΦ`. Establish `hΦs : Φ ∈ schA F _` using `(h₀ _ hsb).2`. Take `⟨y₀, hy⟩` from `Function.ne_iff.1 h0`. Establish `hΦy : Φ (putA v x₀ y₀) = M.vac v y₀`. Express the relevant statement in the definitionally equal form `M.vac v (evA _ v (putA v x₀ y₀)) * r₀ (putA v x₀ y₀) = _`.

Rewrite using `[ev_put (evA_inA v), inv_putA v (h₀ _ hsb).1, h₁, mul_one]`. Establish `hΦ0 : Φ ≠ 0` using `fun e => hy (by rw [← hΦy, e]; rfl)`. Establish `q1 : PresD v X g.1.1` using `presD_of fun z z' a b => ((hK g).1 hk).2 z z' a b g (.inl rfl)`. Establish `q2 : PresD v X (g⁻¹).1.1` using `presD_of fun z z' a b => ((hK g).1 hk).2 z z' a b g⁻¹ (.inr rfl)`. Take `⟨c, hc⟩` from `_root_.PositivityTheory.ThKG.Loc.Cone.Vf.dbl_eigen_k hB hX hW vd hd' hdd hsp.toIsSplitting g hg q2`.

It suffices to establish `h : c = 1 by rwa [h, one_smul] at hc`. Take `⟨g₁, m₁, g₂, m₂, g₃, m₃, g₄, m₄, eg⟩` from `q1`. Take `⟨a₁, n₁, a₂, n₂, a₃, -, a₄, -, ea⟩` from `q2`. Establish `hD : g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E)) = Matrix.fromRows (g₁ + g₂) (g₃ + g₄)`. Rewrite using `[eg, diagCols, Matrix.fromBlocks_mul_fromRows]`.

Simplify using the standard rewrite rules. Establish `hI : a₁ * (g₁ + g₂) + a₂ * (g₃ + g₄) = 1`. Establish `: (g⁻¹).1.1 * (g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E))) = diagCols (Fin n)`. Rewrite using `[← Matrix.mul_assoc, show (g⁻¹).1.1 * g.1.1 = 1 from g.1.inv_mul, Matrix.one_mul]`. Rewrite `this` using `[hD, ea, Matrix.fromBlocks_mul_fromRows, diagCols]`.

Conclude with `(Matrix.fromRows_inj this).1`. Establish `aD` using `at_mul_left (M := g.1.1 - 1) hg (diagCols (Fin n) : Matrix _ _ (AE F E))`. Rewrite `aD` using `[Matrix.sub_mul, Matrix.one_mul, hD]`. Establish `ax : At (evFin F v) (g₁ + g₂ - 1)` using `fun u hu => congrArg Matrix.toRows₁ (aD u hu)`. Establish `ay : At (evFin F v) (g₃ + g₄ - 1)` using `fun u hu => congrArg Matrix.toRows₂ (aD u hu)`.

Establish `px` using `add_mem m₁ m₂`. Establish `py` using `add_mem m₃ m₄`. Generalize the expression as in `g₁ + g₂ = x at *`. Generalize the expression as in `g₃ + g₄ = y at *`. Take `⟨b, b', t', b1, hb, pb, pt, ht⟩` from `_root_.GlobalTheory.ThK.Dbl.Vf2.exists_beta_k hB hX g hD px py n₁ n₂ hI ax ay`.

Establish `hm : At (evFin F v) (y - x)` using `by simpa using at_sub ay ax`. Establish `pm` using `sub_mem py px`. Take `⟨s₀, n₀, p, t, ss, eg', es, en, en', hn, hp, et, et'⟩` from `Vf2.exists_decomp b1 hb g hD ht (ε := PositivityTheory.ThKG.Loc.Cone.Vf.eps v) eps_mul ((cA σ).commutes _) (eps_smul hm)`. Establish `o1` using `one_mem (Pres v X)`. Establish `z0` using `zero_mem (Pres v X)`.

Establish `pC : PresD v X (CC b)` using `⟨_, o1, _, add_mem o1 pb, _, o1, _, pb, rfl⟩`. Establish `pCi : PresD v X (Ci b)` using `⟨_, neg_mem pb, _, add_mem o1 pb, _, o1, _, neg_mem o1, rfl⟩`. Establish `c1 : compFin F E v (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) = 1` using `by rw [PositivityTheory.ThKG.Loc.Cone.Vf.eps, comp_alg, ev_sg]; rfl`. Establish `pe : (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X` using `smul_mem_Pres hL (by rw [c1]; exact one_mem _) o1`. Establish `pe' : (1 - PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X` using `smul_mem_Pres hL (by rw [map_sub, map_one, c1, sub_self]; exact zero_mem _) o1`.

Establish `bt : boxFun Φ (star Φ) = tens (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀))`. Use function extensionality and compare the values at `x`. Simplify using `only [hΦ, boxFun, tens, Pi.star_apply, star_mul']`. Conclude with `mul_mul_mul_comm _ _ _ _`. Establish `hΦd` using `GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Φ hΦs _ (star_mem_schA hΦs)`.

Establish `hd0 : boxFun Φ (star Φ) ≠ 0` using `fun e => lDiag_ne hΦs hΦ0 (by rw [e, map_zero])`. Establish `rd : Rest (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀))`. Use `⟨fun x z hz => ?_, bt ▸ hΦd⟩` and prove the remaining obligations. Establish `i1` using `(h₀ _ hsb).1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _`. Establish `i2` using `(h₀ _ hsb).1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _`.

Express the relevant statement in the definitionally equal form `r₀ (x ∘ Sum.inl + z ∘ Sum.inl) * star (r₀ (x ∘ Sum.inr + z ∘ Sum.inr)) = _`. Rewrite using `[i1, i2]`. Both sides reduce to the same expression. Establish `ev : ∀ g : UG (cA σ) (dbl (incM F X.J)), At (evFin F v) (g.1.1 - 1) → PresD v X (g⁻¹).1.1 → ∃ a : ℂ, omd g (boxFun Φ (star Φ)) = a • boxFun Φ (star Φ)` using `fun g h1 h2 => by`. Take `⟨a, ha⟩` from `_root_.PositivityTheory.ThKG.Loc.Cone.Vf.dbl_eigen_k hB hX hW vd hd' hdd hsp.toIsSplitting g h1 h2`.

Conclude with `⟨a, by rw [bt, ha _ rd, tens_smul]⟩`. Take `⟨a, ha⟩` from `ev s₀ (by`. Rewrite using `[es]`. Use `at_conj (CC_Ci b) fun u hu => ?_` and prove the remaining obligations. Establish `: u • (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) = 0` using `at_eps u hu`.

Rewrite using `[SS, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]`. Simplify using `only [sub_smul, one_smul, neg_zero, add_zero, ← sub_eq_add_neg, sub_sub_cancel_left, smul_neg, ← smul_assoc, this, zero_smul, Matrix.fromBlocks_zero])`. Use the proof step `(by rw [inv_eq_of_mul_eq_one_right ss, es]; exact (pC.mul ⟨_, pe', _, pe, _, pe, _, pe', rfl⟩).mul pCi)`. Take `⟨a', ha'⟩` from `ev n₀ (by`. Rewrite using `[en]`.

Use `at_conj (CC_Ci b) fun u hu => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]`. Simplify using `only [add_neg_cancel, neg_zero, add_zero, smul_zero, smul_neg]`. Rewrite using `[at_mul_left hm t' u hu, neg_zero, Matrix.fromBlocks_zero])`. Use the proof step `(by rw [en']; exact (pC.mul ⟨_, o1, _, mul_mem pm pt, _, z0, _, o1, rfl⟩).mul pCi)`.

Establish `a1 : a' = 1`. Rewrite using `[rule_diag hdd hrule n₀ 1 hn (by rw [map_one, map_one]) hΦs hΦ0 ha']`. Simplify using the standard rewrite rules. Establish `aa : a * a = 1`. Establish `e : omd (s₀ * s₀) (boxFun Φ (star Φ)) = (a * a) • boxFun Φ (star Φ)`.

Rewrite using `[map_mul, Module.End.mul_apply, ha, map_smul, ha, smul_smul]`. Rewrite `e` using `[ss, map_one, Module.End.one_apply]`. Conclude with `smul_left_injective ℂ hd0 (e.symm.trans (one_smul _ _).symm)`. Establish `e1 : omd g (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ)` using `by rw [bt, hc _ rd, tens_smul]`. Establish `e2 : omd p (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ)`.

Establish `e3 : omd (s₀ * n₀ * s₀) (boxFun Φ (star Φ)) = boxFun Φ (star Φ)`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, map_smul, ha', a1, one_smul, map_smul, ha, smul_smul, aa, one_smul]`. Establish `: p = (s₀ * n₀ * s₀)⁻¹ * g` using `by rw [eg']; group`. Rewrite using `[this, map_mul, Module.End.mul_apply, e1, map_smul]`. Use `conv_lhs => rw [← e3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]`.

Both sides reduce to the same expression. Establish `hpos` using `rule_diag hdd hrule p t hp (chi_det hL χ hv t (by rw [et]; exact add_mem py (mul_mem pb pm)) (by rw [et']; exact pt) (by rw [et, add_sub_right_comm]; exact at_add ay (at_mul_right _ hm))) hΦs hΦ0 e2`. Establish `n4` using `Bad.norm_eig hsp.unit hsp.pres hΦd hd0 e1`. Rewrite `n4`, the goal using `[hpos]`. Rewrite `n4` using `[Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]`.

Rewrite using `[n4, Complex.ofReal_one]`.
-/
theorem _root_.GlobalTheory.ThK.Dbl.vacFix2_k : _root_.GlobalTheory.ThK.Dbl.VacFix2_k := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM χ _ dd omd ⟨d', hd', hdd⟩ ⟨_, hsp, hrule⟩ K hK v hv g hk hg
  have hL := hX.lat
  have vd := hM.vac v
  obtain ⟨hsb, h0, -⟩ := hM.vac v
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  set Φ := tens (evFin F v) (M.vac v) r₀ with hΦ
  have hΦs : Φ ∈ schA F _ := (h₀ _ hsb).2
  obtain ⟨y₀, hy⟩ := Function.ne_iff.1 h0
  have hΦy : Φ (putA v x₀ y₀) = M.vac v y₀ := by
    change M.vac v (evA _ v (putA v x₀ y₀)) * r₀ (putA v x₀ y₀) = _
    rw [ev_put (evA_inA v), inv_putA v (h₀ _ hsb).1, h₁, mul_one]
  have hΦ0 : Φ ≠ 0 := fun e => hy (by rw [← hΦy, e]; rfl)
  have q1 : PresD v X g.1.1 := presD_of fun z z' a b => ((hK g).1 hk).2 z z' a b g (.inl rfl)
  have q2 : PresD v X (g⁻¹).1.1 := presD_of fun z z' a b => ((hK g).1 hk).2 z z' a b g⁻¹ (.inr rfl)
  obtain ⟨c, hc⟩ := _root_.PositivityTheory.ThKG.Loc.Cone.Vf.dbl_eigen_k hB hX hW vd hd' hdd hsp.toIsSplitting g hg q2
  suffices h : c = 1 by rwa [h, one_smul] at hc
  obtain ⟨g₁, m₁, g₂, m₂, g₃, m₃, g₄, m₄, eg⟩ := q1
  obtain ⟨a₁, n₁, a₂, n₂, a₃, -, a₄, -, ea⟩ := q2
  have hD : g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E)) = Matrix.fromRows (g₁ + g₂) (g₃ + g₄) := by
    rw [eg, diagCols, Matrix.fromBlocks_mul_fromRows]; simp
  have hI : a₁ * (g₁ + g₂) + a₂ * (g₃ + g₄) = 1 := by
    have : (g⁻¹).1.1 * (g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E))) = diagCols (Fin n) := by
      rw [← Matrix.mul_assoc, show (g⁻¹).1.1 * g.1.1 = 1 from g.1.inv_mul, Matrix.one_mul]
    rw [hD, ea, Matrix.fromBlocks_mul_fromRows, diagCols] at this
    exact (Matrix.fromRows_inj this).1
  have aD := at_mul_left (M := g.1.1 - 1) hg (diagCols (Fin n) : Matrix _ _ (AE F E))
  rw [Matrix.sub_mul, Matrix.one_mul, hD] at aD
  have ax : At (evFin F v) (g₁ + g₂ - 1) := fun u hu => congrArg Matrix.toRows₁ (aD u hu)
  have ay : At (evFin F v) (g₃ + g₄ - 1) := fun u hu => congrArg Matrix.toRows₂ (aD u hu)
  have px := add_mem m₁ m₂
  have py := add_mem m₃ m₄
  generalize g₁ + g₂ = x at *
  generalize g₃ + g₄ = y at *
  obtain ⟨b, b', t', b1, hb, pb, pt, ht⟩ := _root_.GlobalTheory.ThK.Dbl.Vf2.exists_beta_k hB hX g hD px py n₁ n₂ hI ax ay
  have hm : At (evFin F v) (y - x) := by simpa using at_sub ay ax
  have pm := sub_mem py px
  obtain ⟨s₀, n₀, p, t, ss, eg', es, en, en', hn, hp, et, et'⟩ :=
    Vf2.exists_decomp b1 hb g hD ht (ε := PositivityTheory.ThKG.Loc.Cone.Vf.eps v) eps_mul ((cA σ).commutes _) (eps_smul hm)
  have o1 := one_mem (Pres v X)
  have z0 := zero_mem (Pres v X)
  have pC : PresD v X (CC b) := ⟨_, o1, _, add_mem o1 pb, _, o1, _, pb, rfl⟩
  have pCi : PresD v X (Ci b) := ⟨_, neg_mem pb, _, add_mem o1 pb, _, o1, _, neg_mem o1, rfl⟩
  have c1 : compFin F E v (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) = 1 := by rw [PositivityTheory.ThKG.Loc.Cone.Vf.eps, comp_alg, ev_sg]; rfl
  have pe : (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X := smul_mem_Pres hL (by rw [c1]; exact one_mem _) o1
  have pe' : (1 - PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X :=
    smul_mem_Pres hL (by rw [map_sub, map_one, c1, sub_self]; exact zero_mem _) o1
  have bt : boxFun Φ (star Φ) = tens (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    funext x
    simp only [hΦ, boxFun, tens, Pi.star_apply, star_mul']
    exact mul_mul_mul_comm _ _ _ _
  have hΦd := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Φ hΦs _ (star_mem_schA hΦs)
  have hd0 : boxFun Φ (star Φ) ≠ 0 := fun e => lDiag_ne hΦs hΦ0 (by rw [e, map_zero])
  have rd : Rest (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    refine ⟨fun x z hz => ?_, bt ▸ hΦd⟩
    have i1 := (h₀ _ hsb).1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _
    have i2 := (h₀ _ hsb).1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _
    change r₀ (x ∘ Sum.inl + z ∘ Sum.inl) * star (r₀ (x ∘ Sum.inr + z ∘ Sum.inr)) = _
    rw [i1, i2]; rfl
  have ev : ∀ g : UG (cA σ) (dbl (incM F X.J)), At (evFin F v) (g.1.1 - 1) → PresD v X (g⁻¹).1.1 →
      ∃ a : ℂ, omd g (boxFun Φ (star Φ)) = a • boxFun Φ (star Φ) := fun g h1 h2 => by
    obtain ⟨a, ha⟩ := _root_.PositivityTheory.ThKG.Loc.Cone.Vf.dbl_eigen_k hB hX hW vd hd' hdd hsp.toIsSplitting g h1 h2
    exact ⟨a, by rw [bt, ha _ rd, tens_smul]⟩
  obtain ⟨a, ha⟩ := ev s₀ (by
      rw [es]
      refine at_conj (CC_Ci b) fun u hu => ?_
      have : u • (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) = 0 := at_eps u hu
      rw [SS, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
      simp only [sub_smul, one_smul, neg_zero, add_zero, ← sub_eq_add_neg, sub_sub_cancel_left, smul_neg, ← smul_assoc, this,
        zero_smul, Matrix.fromBlocks_zero])
    (by rw [inv_eq_of_mul_eq_one_right ss, es]; exact (pC.mul ⟨_, pe', _, pe, _, pe, _, pe', rfl⟩).mul pCi)
  obtain ⟨a', ha'⟩ := ev n₀ (by
      rw [en]
      refine at_conj (CC_Ci b) fun u hu => ?_
      rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
      simp only [add_neg_cancel, neg_zero, add_zero, smul_zero, smul_neg]
      rw [at_mul_left hm t' u hu, neg_zero, Matrix.fromBlocks_zero])
    (by rw [en']; exact (pC.mul ⟨_, o1, _, mul_mem pm pt, _, z0, _, o1, rfl⟩).mul pCi)
  have a1 : a' = 1 := by
    rw [rule_diag hdd hrule n₀ 1 hn (by rw [map_one, map_one]) hΦs hΦ0 ha']
    simp
  have aa : a * a = 1 := by
    have e : omd (s₀ * s₀) (boxFun Φ (star Φ)) = (a * a) • boxFun Φ (star Φ) := by
      rw [map_mul, Module.End.mul_apply, ha, map_smul, ha, smul_smul]
    rw [ss, map_one, Module.End.one_apply] at e
    exact smul_left_injective ℂ hd0 (e.symm.trans (one_smul _ _).symm)
  have e1 : omd g (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by rw [bt, hc _ rd, tens_smul]
  have e2 : omd p (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by
    have e3 : omd (s₀ * n₀ * s₀) (boxFun Φ (star Φ)) = boxFun Φ (star Φ) := by
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, map_smul, ha', a1, one_smul, map_smul, ha, smul_smul,
        aa, one_smul]
    have : p = (s₀ * n₀ * s₀)⁻¹ * g := by rw [eg']; group
    rw [this, map_mul, Module.End.mul_apply, e1, map_smul]
    conv_lhs => rw [← e3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hpos := rule_diag hdd hrule p t hp (chi_det hL χ hv t (by rw [et]; exact add_mem py (mul_mem pb pm)) (by rw [et']; exact pt)
    (by rw [et, add_sub_right_comm]; exact at_add ay (at_mul_right _ hm))) hΦs hΦ0 e2
  have n4 := Bad.norm_eig hsp.unit hsp.pres hΦd hd0 e1
  rw [hpos] at n4 ⊢
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at n4
  rw [n4, Complex.ofReal_one]
end GlobalTheory.ThK.Dbl.Vf2
end
end
