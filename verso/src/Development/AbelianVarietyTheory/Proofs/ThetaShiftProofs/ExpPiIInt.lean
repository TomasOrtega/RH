import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FinrankHomComplex

noncomputable section

namespace GlobalTheory.OfPeriod

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Complex

/- English proof (translation)
Rewrite using `[← Complex.exp_pi_mul_I, ← Complex.exp_int_mul, mul_comm]`. Simplify using the standard rewrite rules.
-/
theorem exp_pi_I_int (n : ℤ) : Complex.exp (Real.pi * I * ((n : ℝ) : ℂ)) = (-1) ^ n := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul, mul_comm]; simp

variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W] [FiniteDimensional ℂ W]
  {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {O : Type} [CommRing O] [StarRing O]
  {Y M : Type} [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
  [AddCommGroup M] [Module O M] [Module.Free ℤ M] [Module.Finite ℤ M]

/- English proof (translation)
Establish `: FiniteDimensional ℝ W` using `Module.Finite.trans ℂ W`. Set `R : Submodule ℝ W` to `Submodule.span ℝ (Set.range fun n => P (0, n, 0))`. Establish `hmem : ∀ n, P (0, n, 0) ∈ R` using `fun n => Submodule.subset_span ⟨n, rfl⟩`. Establish `hRind : ∀ z, (∀ n, (S z (P (0, n, 0))).im = 0) → ∀ r ∈ R, (S z r).im = 0` using `fun z hz r hr => LinearMap.eqOn_span (f := imForm S z) (g := 0) (by rintro _ ⟨n, rfl⟩; exact hz n) hr`. Establish `him : ∀ z z', (S z z').im = -(S z' z).im` using `fun z z' => by rw [← hconj z z', conj_im, neg_neg]`.

Establish `hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0` using `fun r hr => hRind r fun n => by`. Rewrite using `[him, hRind _ (fun n' => by simp [hS]) r hr, neg_zero]`. Establish `hρR : ∀ a, ∀ r ∈ R, ρ a r ∈ R` using `fun a r hr => by`. Use `Submodule.span_le (p := R.comap ((ρ a).restrictScalars ℝ)).2 ?_ hr` and prove the remaining obligations. Introduce and unpack `_ ⟨n, rfl⟩`.

Use `show ρ a (P (0, n, 0)) ∈ R`. Rewrite using `[← hP]`. Simplify using `using hmem _`. Take `⟨b, hb, hb'⟩` from `exists_imPart hpos hR`. Take `⟨n, q, j, F, hF, hqj, hj, hdec, hjq, hjF⟩` from `exists_compl hpos hb hb' hρ hρR Q hQ`.

Establish `hjinj : Function.Injective j` using `Function.LeftInverse.injective hqj`. Establish `hj' : ∀ z, ∀ r ∈ R, S r (j z) = 0` using `fun z r hr => by rw [← hconj, hj z r hr, map_zero]`. Establish `hbR : ∀ r ∈ R, b r = 0` using `fun r hr => imPart_eq hpos hb hb' R.zero_mem fun r' hr' => by simp [hR r hr r' hr']`. Establish `hbI : ∀ r ∈ R, b (I • r) = r` using `fun r hr => imPart_eq hpos hb hb' hr fun r' hr' => by simp`. Establish `hqR : ∀ r ∈ R, q r = 0` using `fun r hr => hjinj (by simpa [hbR r hr, hbI r hr] using hdec r)`.

Establish `hqρ : ∀ a z, q (ρ a z) = F a (q z)` using `fun a z => by conv_lhs => rw [hdec z]`. Simplify using `only [map_add, map_smul, hqR _ (hρR _ _ (hb _)), ← hjF, hqj, smul_zero, zero_add]`. Establish `hSq : ∀ z z', S z (j z') = S (j (q z)) (j z')` using `fun z z' => by conv_lhs => rw [hdec z]`. Simplify using `[hj' _ _ (hb _)]`. Establish `hbm : ∀ v : Y × (Y →+ ℤ) × M, v.1 = 0 → b (P v) = 0` using `fun v hv => imPart_eq hpos hb hb' R.zero_mem fun r hr => by`.

Rewrite using `[hRind _ (fun n => by simp [hS, hv]) r hr]; simp`. Set `Φ : W → W → ℂ` to `fun z z' => S z (b z') - S (j (q z)) (j (q z')) / (2 * I)`. Establish `hΦ : ∀ z z', Φ z z' = Φ z' z - (S z z').im` using `fun z z' => sub_swap hconj hR hb (hj _) (hj _) (hdec z) (hdec z')`. Establish `hΦρ : ∀ a z z', Φ (ρ a z) z' = Φ z (ρ (star a) z')` using `fun a z z' => by`. Simplify using `only [Φ, hqρ, hjF, hρ, imPart_act hpos hb hb' hρ hρR]`.

Set `s : Y →+ W` to `P.comp (AddMonoidHom.inl _ _)`. Establish `hs : ∀ y, s y = P (y, 0, 0)` using `fun _ => rfl`. Establish `hsρ : ∀ (a : O) y, s (a • y) = ρ a (s y)` using `fun a y => by rw [hs, hs, ← hP]; simp`. Set `φ : W →ₗ[ℂ] (Y →+ ℂ)` to `{ toFun := fun z => AddMonoidHom.mk' (fun x => Φ z (s x)) fun x x' => by simp only [Φ, map_add]; ring map_add' := fun z z' => AddMonoidHom.ext fun x => by simp [Φ]; ring map_smul' := fun c z => AddMonoidHom.ext fun x => by simp [Φ]; ring }`. Establish `hφ : ∀ z x, φ z x = Φ z (s x)` using `fun _ _ => rfl`.

Establish `hPv : ∀ v : Y × (Y →+ ℤ) × M, P v = s v.1 + P (0, v.2.1, 0) + P (0, 0, v.2.2)` using `fun v => by`. Rewrite using `[hs, ← map_add, ← map_add]`. Simplify using the standard rewrite rules. Establish `hφP : ∀ v x, φ (P v) x = φ (s v.1) x + v.2.1 x - S (j (q (s x))) (j (q (P (0, 0, v.2.2)))) / (2 * I)` using `fun v x => by`. Establish `h1 : φ (P (0, v.2.1, 0)) x = v.2.1 x`.

Rewrite using `[hφ, hΦ, hs, hS]`. Simplify using `[Φ, hbm, hqR _ (hmem _)]`. Establish `h2 : φ (P (0, 0, v.2.2)) x = -(S (j (q (s x))) (j (q (P (0, 0, v.2.2)))) / (2 * I))`. Rewrite using `[hφ, hΦ, hs, hS]`. Simplify using `[Φ, hbm]`.

Rewrite using `[hPv v, map_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hr0 : ∀ r ∈ R, (∀ x, (S (s x) r).im = 0) → r = 0` using `fun r hr h0 => by`. Establish `h1 : (imForm S).flip r = 0` using `LinearMap.ext_on_range hspan fun v => by show (S (P v) r).im = 0`. Establish `h2` using `congrArg Complex.re (hb' (P (0, 0, v.2.2)) r hr)`.

Rewrite `h2` using `[hbm _ rfl]`. Rewrite using `[hPv]`. Simplify using `only [map_add, LinearMap.add_apply, add_im, h0, hR _ (hmem _) r hr, zero_add]`. Simplify using `using h2.symm`. Assume the negation of the conclusion as `hne`.

Establish `h3 : (S (I • r) r).im = 0` using `congr($h1 (I • r))`. Conclude with `(hpos r hne).ne' (by simpa using h3)`. Establish `hbij : Function.Bijective (φ.prod q)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `z hz`. Establish `h1 : q z = 0` using `congrArg Prod.snd hz`. Establish `h2 : ∀ x, S z (b (s x)) = 0` using `fun x => by`. Establish `: φ z x = 0` using `congr(($hz).1 x)`. Simplify `this` using `[hφ, Φ, h1]`.

Establish `h3 : ∀ x, (S (s x) (b (I • z))).im = 0 ∧ (S (s x) (b z)).im = 0` using `fun x => by`. Use `h2 x` as an intermediate fact. Rewrite `this` using `[hdec z, h1]`. Simplify using `only [map_add, map_smul, map_zero, add_zero, LinearMap.add_apply, LinearMap.smul_apply, apply_imPart hconj hb' _ (hb _), smul_eq_mul] at this`. Simplify `this` using `[Complex.ext_iff]`.

Rewrite using `[hdec z, h1, hr0 _ (hb _) fun x => (h3 x).1, hr0 _ (hb _) fun x => (h3 x).2]`. Simplify using the standard rewrite rules. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff]`. Introduce and unpack `⟨l, z⟩ -`. Establish `h1 : ∀ l : Y →+ ℂ, (l, (0 : Fin n → ℂ)) ∈ LinearMap.range (φ.prod q)` using `fun l => by`.

Establish `: l ∈ (LinearMap.range (φ.prod q)).comap (LinearMap.inl ℂ _ _)`. Use `(Submodule.span_le.2 ?_) (span_intHom.ge (Submodule.mem_top (x := l)))` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Use `⟨P (0, k, 0), Prod.ext (AddMonoidHom.ext fun x => ?_) (hqR _ (hmem k))⟩` and prove the remaining obligations. Use `show φ _ x = _`.

Rewrite using `[hφP]`. Simplify using `[← Prod.zero_eq_mk]`. Conclude with `this`. Establish `h2 : (l, z) = (l - φ (j z), 0) + φ.prod q (j z)` using `by simp [hqj]`. Rewrite using `[h2]`.

Conclude with `Submodule.add_mem _ (h1 _) ⟨_, rfl⟩`. Set `h : W ≃ₗ[ℂ] (Y →+ ℂ) × (Fin n → ℂ)` to `LinearEquiv.ofBijective _ hbij`. Establish `hrk' : Module.finrank ℤ M = Module.finrank ℝ (Fin n → ℂ)`. Establish `: Module.Finite ℂ (Y →+ ℂ)` using `Module.Finite.equiv (addMonoidHomLequivInt ℂ (A := Y) (B := ℂ)).symm`. Establish `h1` using `h.finrank_eq`.

Rewrite `h1` using `[Module.finrank_prod, finrank_hom_complex, Module.finrank_fin_fun]`. Rewrite using `[finrank_real_of_complex, Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Set `SB : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ⋆[ℂ] ℂ` to `(S ∘ₗ j).compl₂ j`. Establish `hSB : ∀ z z', SB z z' = S (j z) (j z')` using `fun _ _ => rfl`.

Set `Hm : Matrix (Fin n) (Fin n) ℂ` to `Matrix.of fun i k => SB (Pi.single i 1) (Pi.single k 1)`. Establish `hHm : ∀ z z', hermForm Hm z z' = S (j z) (j z')` using `sesq_of SB`. Set `p : M →+ (Fin n → ℂ)` to `q.toAddMonoidHom.comp (P.comp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inr _ _)))`. Establish `hp : ∀ m, p m = q (P (0, 0, m))` using `fun _ => rfl`. Establish `hpE : ∀ m m', (S (j (p m)) (j (p m'))).im = EM m m'` using `fun m m' => by`.

Establish `h1` using `hΦ (P (0, 0, m)) (P (0, 0, m'))`. Simplify using `only [Φ, hbm (0, 0, _) rfl, map_zero, hS, ← hp, AnArc.div_two_I] at h1`. Establish `h2` using `congrArg Complex.re h1`. Simplify using `[him (j (p m')) (j (p m))] at h2`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hpF : ∀ (a : O) m, p (a • m) = F a (p m)` using `fun a m => by`. Rewrite using `[hp, hp, ← hqρ, ← hP]`. Simplify using the standard rewrite rules. Take `⟨hpi, hpd, hps⟩` from `PolarisedLattice.lattice_of_im EM hEM.1 p (fun z => SB.flip z) hpE hrk'`. Set `f : M ≃ₗ[ℤ] LinearMap.range p.toIntLinearMap` to `LinearEquiv.ofInjective p.toIntLinearMap hpi`.

Establish `hf : ∀ m, (f m : Fin n → ℂ) = p m` using `fun _ => rfl`. Set `Ef` to `LinearMap.BilinForm.congr f EM`. Establish `hEf : ∀ m m', Ef (f m) (f m') = EM m m'` using `fun m m' => by`. Rewrite using `[LinearMap.BilinForm.congr_apply, f.symm_apply_apply, f.symm_apply_apply]`. Establish `hEadj : ∀ (a : O) m m', EM (a • m) m' = EM m (star a • m')` using `fun a m m' => by`.

Establish `: (EM (a • m) m' : ℝ) = EM m (star a • m')` using `by rw [← hpE, ← hpE, hpF, hpF, hjF, hjF, hρ]`. Conclude with `this` after adjusting the coercions. Establish `hEalt : ∀ m m', EM m m' = -EM m' m` using `fun m m' => by`. Establish `: (EM m m' : ℝ) = -EM m' m` using `by rw [← hpE, ← hpE, him]`. Conclude with `this` after adjusting the coercions.

Establish `hTs : ∀ x y, φ (s x) y = φ (s y) x` using `fun x y => by rw [hφ, hφ, hΦ, hs, hs, hS]; simp`. Establish `hTa : ∀ (a : O) y x, φ (s (a • y)) x = φ (s y) (star a • x)` using `fun a y x => by`. Rewrite using `[hφ, hφ, hsρ, hsρ, hΦρ]`. Set `A : AnArc O` to `{ gB := n abelian₂ := LinearMap.range p.toIntLinearMap discrete := hpd full := hps Hm := Hm Hm_herm := by ext i k; exact hconj _ _ Hm_pos := fun z hz => by rw [hHm]; exact hpos _ fun h0 => hz (hjinj (by rw [h0, map_zero])) Ef := Ef Ef_eq := fun l m => by`. Take `⟨l, rfl⟩` from `f.surjective l`.

Take `⟨m, rfl⟩` from `f.surjective m`. Rewrite using `[hEf, hHm, hf, hf, hpE]`. Use `Ef_bij := by`. Establish `: (Ef : _ → _) = f.symm.dualMap ∘ EM ∘ f.symm` using `rfl`. Rewrite using `[this]`.

Conclude with `f.symm.dualMap.bijective.comp (hEM.comp f.symm.bijective)`. Use `chi := fun l => (-1) ^ EM (w • f.symm l) (f.symm l)`. Use `chi_norm := fun l => by simp`. Use `chi_add := fun l m => by`. Take `⟨l, rfl⟩` from `f.surjective l`.

Take `⟨m, rfl⟩` from `f.surjective m`. Establish `h1 : EM (w • (l + m)) (l + m) = EM (w • l) l + EM (w • m) m + EM l m + 2 * (EM (w • l) m - EM l m)`. Establish `h2 : EM (w • l) m + EM (star w • l) m = EM l m`. Rewrite using `[← LinearMap.add_apply, ← map_add, ← add_smul, hw, one_smul]`. Establish `h3 : EM (w • m) l = -EM (star w • l) m` using `by rw [hEadj, hEalt]`.

Simplify using `only [smul_add, map_add, LinearMap.add_apply]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hHm, hf, hf, hpE, exp_pi_I_int, ← map_add f]`. Simplify using `only [LinearEquiv.symm_apply_apply, h1, zpow_add₀ (neg_ne_zero.2 (one_ne_zero (α := ℂ))), zpow_mul]`. Simplify using the standard rewrite rules.

Use `chi_neg := fun l => by simp only [map_neg, smul_neg, LinearMap.neg_apply, neg_neg]`. Use `F := F`. Use `F_mem := by rintro a _ ⟨m, rfl⟩; exact ⟨a • m, hpF a m⟩`. Use `F_adj := fun a z z' => by rw [hHm, hHm, hjF, hjF, hρ]`. Use `X := Y`.

Use `ct := q.toAddMonoidHom.comp s`. Use `ct_smul := fun a x => by show q (s (a • x)) = F a (q (s x))`. Rewrite using `[hsρ, hqρ]`. Use `T := φ.toAddMonoidHom.comp s`. Use `T_symm := hTs`.

Use `T_adj := hTa`. Use `psi := fun x => Units.mk0 (eTwoPi (φ (s x) (w • x))) (AnArc.e_ne_zero _)`. Use `psi_neg := fun x => by simp`. Use `psi_add := fun x y => by`. Establish `h2 : φ (s x) (w • y) + φ (s y) (w • x) = φ (s x) y`.

Rewrite using `[hTs y, hTa, ← map_add, ← add_smul, hw, one_smul]`. Express the relevant statement in the definitionally equal form `eTwoPi _ = eTwoPi _ * eTwoPi _ * eTwoPi (φ (s x) y)`. Simplify using `only [← AnArc.e_add, smul_add, map_add, AddMonoidHom.add_apply]`. Use `congr 1`. Take the linear combination `h2`.

Use `be := be`. Use `be_symm := be_symm`. Use `be_pos := be_pos`. Use `be_adj := be_adj`. Use `be_even := be_even }`.

Establish `hfF : ∀ (a : O) m, f (a • m) = A.FLam a (f m)` using `fun a m => Subtype.ext (hpF a m)`. Use `⟨A, LinearEquiv.refl O Y, f.toAddEquiv, h, fun _ _ => rfl, fun l => ?_, fun _ => rfl, hF, hfF, hEf, fun a z => ?_, fun v => ?_, ?_⟩` and prove the remaining obligations. Take `⟨l, rfl⟩` from `f.surjective l`. Rewrite using `[← hfF]`. Use `show (-1 : ℂ) ^ EM (w • f.symm (f l)) (f.symm (f l)) = (-1) ^ Ef (f (w • l)) (f l)`.

Rewrite using `[hEf, f.symm_apply_apply]`. Use `Prod.ext (AddMonoidHom.ext fun x => ?_) (hqρ a z) show φ (ρ a z) x = φ z (star a • x)` and prove the remaining obligations. Rewrite using `[hφ, hφ, hΦρ, hsρ]`. Use `Prod.ext (AddMonoidHom.ext fun x => ?_) ?_` and prove the remaining obligations. Use `show φ (P v) x = φ (s v.1) x + v.2.1 x - hermForm Hm (q (s x)) (p v.2.2) / (2 * I)`.

Rewrite using `[hφP, hHm, hp]`. Use `show q (P v) = q (s v.1) + p v.2.2`. Rewrite using `[hPv, map_add, map_add, hqR _ (hmem _), add_zero, hp]`. Establish `hB : ∀ y x : Y, A.Bw 0 y x = (S (b (s y)) (b (s x))).re` using `fun y x => by show (φ (s y) x + 0 * (be y x : ℂ) + hermForm Hm (q (s y)) (q (s x)) / (2 * I)).im = _`. Rewrite using `[hφ, hHm, hb' _ _ (hb _)]`.

Simplify using `[Φ]`. Set `c` to `Module.Free.chooseBasis ℤ A.X`. Use `Matrix.posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Use extensionality with `i k`. Simplify using `[AnArc.BwMat_apply, A.Bw_symm 0 (Module.Free.chooseBasis ℤ A.X i)]`.

Establish `h1 : ∑ i, x i • b (s (c i)) ≠ 0` using `fun h0 => hx (funext fun k => by`. Establish `h2` using `congrArg (fun z => reForm S z (P (0, (c.coord k).toAddMonoidHom, 0))) h0`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, reForm_apply, hb' _ _ (hmem _), hs, hS] at h2`. Simplify `h2)` using `[Finsupp.single_apply]`. Use `(hpos _ h1).trans_eq ?_` and prove the remaining obligations.

Rewrite using `[← reForm_apply]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, reForm_apply, ← hB, dotProduct, Matrix.mulVec, AnArc.BwMat_apply, Finset.mul_sum, smul_eq_mul, star_trivial]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by simp only [c]; ring`.
-/
theorem exists_arc {w : O} (hw : w + star w = 1) (EM : LinearMap.BilinForm ℤ M) (hEM : Function.Bijective EM)
    (P : Y × (Y →+ ℤ) × M →+ W) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (hrk : 2 * Module.finrank ℤ Y + Module.finrank ℤ M = 2 * Module.finrank ℂ W)
    (hconj : ∀ z w, starRingEnd ℂ (S z w) = S w z) (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
    (hS : ∀ v v', (S (P v) (P v')).im = (v'.2.1 v.1 - v.2.1 v'.1 + EM v.2.2 v'.2.2 : ℤ))
    (ρ : O →+* Module.End ℂ W) (hρ : ∀ a z w, S (ρ a z) w = S z (ρ (star a) w))
    (hP : ∀ (a : O) v, P (a • v.1, v.2.1.comp (DistribSMul.toAddMonoidHom Y (star a)), a • v.2.2) = ρ a (P v))
    (be : LinearMap.BilinForm ℤ Y) (be_symm : ∀ x y, be x y = be y x) (be_pos : ∀ x, x ≠ 0 → 0 < be x x)
    (be_adj : ∀ (a : O) y x, be (a • y) x = be y (star a • x)) (be_even : ∀ x, (2 : ℤ) ∣ be x x)
    (Q : ∀ n : ℕ, (O →+* Module.End ℂ (Fin n → ℂ)) → Prop)
    (hQ : ∀ (U : Type) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (σ : O →+* Module.End ℂ U),
      ∃ (n : ℕ) (k : U ≃ₗ[ℂ] (Fin n → ℂ)) (F : O →+* Module.End ℂ (Fin n → ℂ)), Q n F ∧ ∀ a u, k (σ a u) = F a (k u)) :
    ∃ (A : AnArc O) (e : A.X ≃ₗ[O] Y) (f : M ≃+ A.abelian₂) (h : W ≃ₗ[ℂ] A.V),
      (∀ x y, A.be x y = be (e x) (e y)) ∧ (∀ l, A.chi l = (-1) ^ A.Ef (A.FLam w l) l) ∧
      (∀ x, (A.psi x : ℂ) = eTwoPi (A.T x (w • x))) ∧ Q A.gB A.F ∧ (∀ (a : O) m, f (a • m) = A.FLam a (f m)) ∧
      (∀ m m', A.Ef (f m) (f m') = EM m m') ∧ (∀ a z, h (ρ a z) = A.actV a (h z)) ∧
      (∀ v, h (P v) = A.P0 (AnArc.La.mk (e.symm v.1) (v.2.1.comp e.toAddEquiv.toAddMonoidHom) (f v.2.2))) ∧
      (A.BwMat 0).PosDef := by
  have : FiniteDimensional ℝ W := Module.Finite.trans ℂ W
  let R : Submodule ℝ W := Submodule.span ℝ (Set.range fun n => P (0, n, 0))
  have hmem : ∀ n, P (0, n, 0) ∈ R := fun n => Submodule.subset_span ⟨n, rfl⟩
  have hRind : ∀ z, (∀ n, (S z (P (0, n, 0))).im = 0) → ∀ r ∈ R, (S z r).im = 0 := fun z hz r hr =>
    LinearMap.eqOn_span (f := imForm S z) (g := 0) (by rintro _ ⟨n, rfl⟩; exact hz n) hr
  have him : ∀ z z', (S z z').im = -(S z' z).im := fun z z' => by rw [← hconj z z', conj_im, neg_neg]
  have hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0 := fun r hr => hRind r fun n => by
    rw [him, hRind _ (fun n' => by simp [hS]) r hr, neg_zero]
  have hρR : ∀ a, ∀ r ∈ R, ρ a r ∈ R := fun a r hr => by
    refine Submodule.span_le (p := R.comap ((ρ a).restrictScalars ℝ)).2 ?_ hr
    rintro _ ⟨n, rfl⟩
    show ρ a (P (0, n, 0)) ∈ R
    rw [← hP]
    simpa using hmem _
  obtain ⟨b, hb, hb'⟩ := exists_imPart hpos hR
  obtain ⟨n, q, j, F, hF, hqj, hj, hdec, hjq, hjF⟩ := exists_compl hpos hb hb' hρ hρR Q hQ
  have hjinj : Function.Injective j := Function.LeftInverse.injective hqj
  have hj' : ∀ z, ∀ r ∈ R, S r (j z) = 0 := fun z r hr => by rw [← hconj, hj z r hr, map_zero]
  have hbR : ∀ r ∈ R, b r = 0 := fun r hr =>
    imPart_eq hpos hb hb' R.zero_mem fun r' hr' => by simp [hR r hr r' hr']
  have hbI : ∀ r ∈ R, b (I • r) = r := fun r hr => imPart_eq hpos hb hb' hr fun r' hr' => by simp
  have hqR : ∀ r ∈ R, q r = 0 := fun r hr => hjinj (by simpa [hbR r hr, hbI r hr] using hdec r)
  have hqρ : ∀ a z, q (ρ a z) = F a (q z) := fun a z => by
    conv_lhs => rw [hdec z]
    simp only [map_add, map_smul, hqR _ (hρR _ _ (hb _)), ← hjF, hqj, smul_zero, zero_add]
  have hSq : ∀ z z', S z (j z') = S (j (q z)) (j z') := fun z z' => by
    conv_lhs => rw [hdec z]
    simp [hj' _ _ (hb _)]
  have hbm : ∀ v : Y × (Y →+ ℤ) × M, v.1 = 0 → b (P v) = 0 := fun v hv =>
    imPart_eq hpos hb hb' R.zero_mem fun r hr => by
      rw [hRind _ (fun n => by simp [hS, hv]) r hr]; simp

  let Φ : W → W → ℂ := fun z z' => S z (b z') - S (j (q z)) (j (q z')) / (2 * I)
  have hΦ : ∀ z z', Φ z z' = Φ z' z - (S z z').im := fun z z' =>
    sub_swap hconj hR hb (hj _) (hj _) (hdec z) (hdec z')
  have hΦρ : ∀ a z z', Φ (ρ a z) z' = Φ z (ρ (star a) z') := fun a z z' => by
    simp only [Φ, hqρ, hjF, hρ, imPart_act hpos hb hb' hρ hρR]
  let s : Y →+ W := P.comp (AddMonoidHom.inl _ _)
  have hs : ∀ y, s y = P (y, 0, 0) := fun _ => rfl
  have hsρ : ∀ (a : O) y, s (a • y) = ρ a (s y) := fun a y => by rw [hs, hs, ← hP]; simp
  let φ : W →ₗ[ℂ] (Y →+ ℂ) :=
    { toFun := fun z => AddMonoidHom.mk' (fun x => Φ z (s x)) fun x x' => by simp only [Φ, map_add]; ring
      map_add' := fun z z' => AddMonoidHom.ext fun x => by simp [Φ]; ring
      map_smul' := fun c z => AddMonoidHom.ext fun x => by simp [Φ]; ring }
  have hφ : ∀ z x, φ z x = Φ z (s x) := fun _ _ => rfl
  have hPv : ∀ v : Y × (Y →+ ℤ) × M, P v = s v.1 + P (0, v.2.1, 0) + P (0, 0, v.2.2) := fun v => by
    rw [hs, ← map_add, ← map_add]; simp
  have hφP : ∀ v x, φ (P v) x = φ (s v.1) x + v.2.1 x - S (j (q (s x))) (j (q (P (0, 0, v.2.2)))) / (2 * I) :=
    fun v x => by
      have h1 : φ (P (0, v.2.1, 0)) x = v.2.1 x := by
        rw [hφ, hΦ, hs, hS]; simp [Φ, hbm, hqR _ (hmem _)]
      have h2 : φ (P (0, 0, v.2.2)) x = -(S (j (q (s x))) (j (q (P (0, 0, v.2.2)))) / (2 * I)) := by
        rw [hφ, hΦ, hs, hS]; simp [Φ, hbm]
      rw [hPv v, map_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, h1, h2]; ring
  have hr0 : ∀ r ∈ R, (∀ x, (S (s x) r).im = 0) → r = 0 := fun r hr h0 => by
    have h1 : (imForm S).flip r = 0 := LinearMap.ext_on_range hspan fun v => by
      show (S (P v) r).im = 0
      have h2 := congrArg Complex.re (hb' (P (0, 0, v.2.2)) r hr)
      rw [hbm _ rfl] at h2
      rw [hPv]
      simp only [map_add, LinearMap.add_apply, add_im, h0, hR _ (hmem _) r hr, zero_add]
      simpa using h2.symm
    by_contra hne
    have h3 : (S (I • r) r).im = 0 := congr($h1 (I • r))
    exact (hpos r hne).ne' (by simpa using h3)
  have hbij : Function.Bijective (φ.prod q) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      have h1 : q z = 0 := congrArg Prod.snd hz
      have h2 : ∀ x, S z (b (s x)) = 0 := fun x => by
        have : φ z x = 0 := congr(($hz).1 x)
        simpa [hφ, Φ, h1] using this
      have h3 : ∀ x, (S (s x) (b (I • z))).im = 0 ∧ (S (s x) (b z)).im = 0 := fun x => by
        have := h2 x
        rw [hdec z, h1] at this
        simp only [map_add, map_smul, map_zero, add_zero, LinearMap.add_apply, LinearMap.smul_apply,
          apply_imPart hconj hb' _ (hb _), smul_eq_mul] at this
        simpa [Complex.ext_iff] using this
      rw [hdec z, h1, hr0 _ (hb _) fun x => (h3 x).1, hr0 _ (hb _) fun x => (h3 x).2]
      simp
    · rw [← LinearMap.range_eq_top, eq_top_iff]
      rintro ⟨l, z⟩ -
      have h1 : ∀ l : Y →+ ℂ, (l, (0 : Fin n → ℂ)) ∈ LinearMap.range (φ.prod q) := fun l => by
        have : l ∈ (LinearMap.range (φ.prod q)).comap (LinearMap.inl ℂ _ _) := by
          refine (Submodule.span_le.2 ?_) (span_intHom.ge (Submodule.mem_top (x := l)))
          rintro _ ⟨k, rfl⟩
          refine ⟨P (0, k, 0), Prod.ext (AddMonoidHom.ext fun x => ?_) (hqR _ (hmem k))⟩
          show φ _ x = _
          rw [hφP]
          simp [← Prod.zero_eq_mk]
        exact this
      have h2 : (l, z) = (l - φ (j z), 0) + φ.prod q (j z) := by simp [hqj]
      rw [h2]
      exact Submodule.add_mem _ (h1 _) ⟨_, rfl⟩
  let h : W ≃ₗ[ℂ] (Y →+ ℂ) × (Fin n → ℂ) := LinearEquiv.ofBijective _ hbij
  have hrk' : Module.finrank ℤ M = Module.finrank ℝ (Fin n → ℂ) := by
    have : Module.Finite ℂ (Y →+ ℂ) := Module.Finite.equiv (addMonoidHomLequivInt ℂ (A := Y) (B := ℂ)).symm
    have h1 := h.finrank_eq
    rw [Module.finrank_prod, finrank_hom_complex, Module.finrank_fin_fun] at h1
    rw [finrank_real_of_complex, Module.finrank_fin_fun]
    omega
  let SB : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ⋆[ℂ] ℂ := (S ∘ₗ j).compl₂ j
  have hSB : ∀ z z', SB z z' = S (j z) (j z') := fun _ _ => rfl
  let Hm : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => SB (Pi.single i 1) (Pi.single k 1)
  have hHm : ∀ z z', hermForm Hm z z' = S (j z) (j z') := sesq_of SB
  let p : M →+ (Fin n → ℂ) :=
    q.toAddMonoidHom.comp (P.comp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inr _ _)))
  have hp : ∀ m, p m = q (P (0, 0, m)) := fun _ => rfl
  have hpE : ∀ m m', (S (j (p m)) (j (p m'))).im = EM m m' := fun m m' => by
    have h1 := hΦ (P (0, 0, m)) (P (0, 0, m'))
    simp only [Φ, hbm (0, 0, _) rfl, map_zero, hS, ← hp, AnArc.div_two_I] at h1
    have h2 := congrArg Complex.re h1
    simp [him (j (p m')) (j (p m))] at h2
    linarith
  have hpF : ∀ (a : O) m, p (a • m) = F a (p m) := fun a m => by
    rw [hp, hp, ← hqρ, ← hP]; simp
  obtain ⟨hpi, hpd, hps⟩ := PolarisedLattice.lattice_of_im EM hEM.1 p (fun z => SB.flip z) hpE hrk'
  let f : M ≃ₗ[ℤ] LinearMap.range p.toIntLinearMap := LinearEquiv.ofInjective p.toIntLinearMap hpi
  have hf : ∀ m, (f m : Fin n → ℂ) = p m := fun _ => rfl
  let Ef := LinearMap.BilinForm.congr f EM
  have hEf : ∀ m m', Ef (f m) (f m') = EM m m' := fun m m' => by
    rw [LinearMap.BilinForm.congr_apply, f.symm_apply_apply, f.symm_apply_apply]
  have hEadj : ∀ (a : O) m m', EM (a • m) m' = EM m (star a • m') := fun a m m' => by
    have : (EM (a • m) m' : ℝ) = EM m (star a • m') := by rw [← hpE, ← hpE, hpF, hpF, hjF, hjF, hρ]
    exact_mod_cast this
  have hEalt : ∀ m m', EM m m' = -EM m' m := fun m m' => by
    have : (EM m m' : ℝ) = -EM m' m := by rw [← hpE, ← hpE, him]
    exact_mod_cast this
  have hTs : ∀ x y, φ (s x) y = φ (s y) x := fun x y => by rw [hφ, hφ, hΦ, hs, hs, hS]; simp
  have hTa : ∀ (a : O) y x, φ (s (a • y)) x = φ (s y) (star a • x) := fun a y x => by
    rw [hφ, hφ, hsρ, hsρ, hΦρ]
  let A : AnArc O :=
    { gB := n
      abelian₂ := LinearMap.range p.toIntLinearMap
      discrete := hpd
      full := hps
      Hm := Hm
      Hm_herm := by ext i k; exact hconj _ _
      Hm_pos := fun z hz => by rw [hHm]; exact hpos _ fun h0 => hz (hjinj (by rw [h0, map_zero]))
      Ef := Ef
      Ef_eq := fun l m => by
        obtain ⟨l, rfl⟩ := f.surjective l
        obtain ⟨m, rfl⟩ := f.surjective m
        rw [hEf, hHm, hf, hf, hpE]
      Ef_bij := by
        have : (Ef : _ → _) = f.symm.dualMap ∘ EM ∘ f.symm := rfl
        rw [this]
        exact f.symm.dualMap.bijective.comp (hEM.comp f.symm.bijective)
      chi := fun l => (-1) ^ EM (w • f.symm l) (f.symm l)
      chi_norm := fun l => by simp
      chi_add := fun l m => by
        obtain ⟨l, rfl⟩ := f.surjective l
        obtain ⟨m, rfl⟩ := f.surjective m
        have h1 : EM (w • (l + m)) (l + m) =
            EM (w • l) l + EM (w • m) m + EM l m + 2 * (EM (w • l) m - EM l m) := by
          have h2 : EM (w • l) m + EM (star w • l) m = EM l m := by
            rw [← LinearMap.add_apply, ← map_add, ← add_smul, hw, one_smul]
          have h3 : EM (w • m) l = -EM (star w • l) m := by rw [hEadj, hEalt]
          simp only [smul_add, map_add, LinearMap.add_apply]
          linarith
        rw [hHm, hf, hf, hpE, exp_pi_I_int, ← map_add f]
        simp only [LinearEquiv.symm_apply_apply, h1, zpow_add₀ (neg_ne_zero.2 (one_ne_zero (α := ℂ))), zpow_mul]
        simp
      chi_neg := fun l => by simp only [map_neg, smul_neg, LinearMap.neg_apply, neg_neg]
      F := F
      F_mem := by rintro a _ ⟨m, rfl⟩; exact ⟨a • m, hpF a m⟩
      F_adj := fun a z z' => by rw [hHm, hHm, hjF, hjF, hρ]
      X := Y
      ct := q.toAddMonoidHom.comp s
      ct_smul := fun a x => by
        show q (s (a • x)) = F a (q (s x))
        rw [hsρ, hqρ]
      T := φ.toAddMonoidHom.comp s
      T_symm := hTs
      T_adj := hTa
      psi := fun x => Units.mk0 (eTwoPi (φ (s x) (w • x))) (AnArc.e_ne_zero _)
      psi_neg := fun x => by simp
      psi_add := fun x y => by
        have h2 : φ (s x) (w • y) + φ (s y) (w • x) = φ (s x) y := by
          rw [hTs y, hTa, ← map_add, ← add_smul, hw, one_smul]
        change eTwoPi _ = eTwoPi _ * eTwoPi _ * eTwoPi (φ (s x) y)
        simp only [← AnArc.e_add, smul_add, map_add, AddMonoidHom.add_apply]
        congr 1
        linear_combination h2
      be := be
      be_symm := be_symm
      be_pos := be_pos
      be_adj := be_adj
      be_even := be_even }
  have hfF : ∀ (a : O) m, f (a • m) = A.FLam a (f m) := fun a m => Subtype.ext (hpF a m)
  refine ⟨A, LinearEquiv.refl O Y, f.toAddEquiv, h, fun _ _ => rfl, fun l => ?_, fun _ => rfl, hF, hfF, hEf,
    fun a z => ?_, fun v => ?_, ?_⟩
  · obtain ⟨l, rfl⟩ := f.surjective l
    rw [← hfF]
    show (-1 : ℂ) ^ EM (w • f.symm (f l)) (f.symm (f l)) = (-1) ^ Ef (f (w • l)) (f l)
    rw [hEf, f.symm_apply_apply]
  · refine Prod.ext (AddMonoidHom.ext fun x => ?_) (hqρ a z)
    show φ (ρ a z) x = φ z (star a • x)
    rw [hφ, hφ, hΦρ, hsρ]
  · refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · show φ (P v) x = φ (s v.1) x + v.2.1 x - hermForm Hm (q (s x)) (p v.2.2) / (2 * I)
      rw [hφP, hHm, hp]
    · show q (P v) = q (s v.1) + p v.2.2
      rw [hPv, map_add, map_add, hqR _ (hmem _), add_zero, hp]
  · have hB : ∀ y x : Y, A.Bw 0 y x = (S (b (s y)) (b (s x))).re := fun y x => by
      show (φ (s y) x + 0 * (be y x : ℂ) + hermForm Hm (q (s y)) (q (s x)) / (2 * I)).im = _
      rw [hφ, hHm, hb' _ _ (hb _)]
      simp [Φ]
    let c := Module.Free.chooseBasis ℤ A.X
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · ext i k; simp [AnArc.BwMat_apply, A.Bw_symm 0 (Module.Free.chooseBasis ℤ A.X i)]
    · have h1 : ∑ i, x i • b (s (c i)) ≠ 0 := fun h0 => hx (funext fun k => by
        have h2 := congrArg (fun z => reForm S z (P (0, (c.coord k).toAddMonoidHom, 0))) h0
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, reForm_apply, hb' _ _ (hmem _), hs,
          hS] at h2
        simpa [Finsupp.single_apply] using h2)
      refine (hpos _ h1).trans_eq ?_
      rw [← reForm_apply]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, reForm_apply, ← hB, dotProduct,
        Matrix.mulVec, AnArc.BwMat_apply, Finset.mul_sum, smul_eq_mul, star_trivial]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by simp only [c]; ring

end GlobalTheory.OfPeriod
