import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransFinA
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransFinF

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace TF

def rc {W : Type*} [AddCommGroup W] [Module ℂ W] (A : Module.End ℂ W) : Module.End ℂ (W →ₗ[ℂ] ℂ) where
  toFun f := f ∘ₗ A
  map_add' f f' := LinearMap.add_comp A f' f
  map_smul' c f := LinearMap.smul_comp c f A

/- English proof (translation)
Use `show rc A * rc B = rc B * rc A`. Use `LinearMap.ext fun f => LinearMap.ext fun w => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f (B (A w)) = f (A (B w))`. Conclude with `congrArg f (LinearMap.congr_fun h.eq.symm w)`.
-/
theorem rc_comm {W : Type*} [AddCommGroup W] [Module ℂ W] (A B : Module.End ℂ W) (h : Commute A B) :
    Commute (rc A) (rc B) := by
  show rc A * rc B = rc B * rc A
  refine LinearMap.ext fun f => LinearMap.ext fun w => ?_
  change f (B (A w)) = f (A (B w))
  exact congrArg f (LinearMap.congr_fun h.eq.symm w)

def lc {W : Type*} [AddCommGroup W] [Module ℂ W] (ψ : W →ₗ[ℂ] ℂ) : Module.End ℂ W →ₗ[ℂ] (W →ₗ[ℂ] ℂ) where
  toFun r := ψ ∘ₗ r
  map_add' r r' := LinearMap.comp_add r r' ψ
  map_smul' c r := by ext; simp

def ev {W : Type*} [AddCommGroup W] [Module ℂ W] (v : W) : (W →ₗ[ℂ] ℂ) →ₗ[ℂ] ℂ where
  toFun f := f v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Use `LinearMap.ext fun f => funext fun I => ?_` and prove the remaining obligations. Simplify using `[lift, Algebra.algebraMap_eq_smul_one]`.
-/
theorem lift_alg {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} (c : ℂ) :
    (lift (algebraMap ℂ (Module.End ℂ M) c) : Module.End ℂ (TV n M P)) = algebraMap ℂ _ c := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp [lift, Algebra.algebraMap_eq_smul_one]

end TF

/- English proof (translation)
Introduce `hT hJ hS hQ hSp hC hCA`. Introduce `n M _ _ E hE l hl ℓ hℓ hW hn m col b co hmono htab hcol`. Set `top : Fin n` to `⟨n - 1, by omega⟩`. Establish `htop : (top : ℕ) + 1 = n` using `by show n - 1 + 1 = n`. Use linear arithmetic over natural numbers and integers.

Establish `hE' : GlRel (tE (Finset.univ : Finset (Fin m)) E)` using `(hT n M (Fin m) E hE Finset.univ).1`. Take `⟨c, hc⟩` from `(hQ n (TV n M (Fin m)) (tE (Finset.univ : Finset (Fin m)) E) hE').2.1`. Use `set B : Subalgebra ℂ (Module.End ℂ (TV n M (Fin m))) := Algebra.adjoin ℂ (Set.range fun j : Fin m => xJ E j) with hB`. Use `set A := envAlg fun _ : Unit => tE (Finset.univ : Finset (Fin m)) E with hA`. Establish `hxcomm : ∀ i j : Fin m, Commute (xJ E i) (xJ E j)` using `(hJ n M E hE m).1`.

Establish `hxB : ∀ j, xJ E j ∈ B` using `fun j => Algebra.subset_adjoin ⟨j, rfl⟩`. Establish `hBcomm : ∀ x ∈ B, ∀ y ∈ B, Commute x y`. Introduce `x hx y hy`. Use `Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `(Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx ?_).symm` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hxcomm j i`. Establish `hcs : ∀ (f : TV n M (Fin m) →ₗ[ℂ] ℂ) (h : ℕ → Module.End ℂ (TV n M (Fin m))), f ∘ₗ (∑ i ∈ Finset.range (n + 1), h i) = ∑ i ∈ Finset.range (n + 1), f ∘ₗ h i`. Introduce `f h`.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `set N : ℤ := ∑ k, |l k| with hN`. Establish `hlN : ∀ k, 0 ≤ l k + N`. Introduce `k`.

Establish `h1 : |l k| ≤ N` using `Finset.single_le_sum (f := fun k => |l k|) (fun k _ => abs_nonneg _) (Finset.mem_univ k)`. Establish `h2` using `neg_abs_le (l k)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsp` using `hSp n M E hE (fun k => (l k : ℂ)) (-(N : ℂ)) hl (fun k => ⟨(l k + N).toNat, by`. Rewrite using `[show (((l k + N).toNat : ℕ) : ℂ) = ((l k + N : ℤ) : ℂ) by`.

Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg (hlN k)]]`. Use `push_cast`. Use the proof step `ring⟩) m`. Use `choose L hL using hsp.2`. Set `L' : Fin m → List ℂ` to `fun j => (L j).map (fun r : ℕ => -(N : ℂ) + r)`.

Establish `hL' : ∀ j, (List.map (fun c => xJ E j - algebraMap ℂ _ c) (L' j)).prod = 0`. Introduce `j`. Rewrite using `[List.map_map]`. Conclude with `hL j`. Use `haveI hBfin : FiniteDimensional ℂ (Subalgebra.toSubmodule B) := TF.fin_adjoin (fun j : Fin m => xJ E j) hxcomm (fun j => ⟨L' j, hL' j⟩)`.

Establish `hlift : ∀ u : ℂ, (lift (qdet E u) : Module.End ℂ (TV n M (Fin m))) = algebraMap ℂ _ (∏ k, (u + (l k : ℂ)))`. Introduce `u`. Rewrite using `[hl u]`. Conclude with `TF.lift_alg _`. Establish `hqB : ∀ u : ℂ, (∀ j : Fin m, ∀ c ∈ L' j, u + c ≠ 0) → qdet (tE Finset.univ E) u ∈ B`.

Introduce `u hu`. Take `⟨h, hhB, hh⟩` from `TF.left_inv_prod B.toSubring (List.ofFn fun j : Fin m => algebraMap ℂ (Module.End ℂ (TV n M (Fin m))) u + xJ E j) (by`. Introduce `a ha`. Take `⟨j, rfl⟩` from `List.mem_ofFn.mp ha`. Conclude with `TF.inv_of_alg B (xJ E j) (hxB j) u (L' j) (hL' j) (hu j))`.

Establish `hstep` using `hS n M E hE m u`. Rewrite `hstep` using `[hlift]`. Establish `e1 : qdet (tE Finset.univ E) u = h * (algebraMap ℂ _ (∏ k, (u + (l k : ℂ))) * PiJ m E (u + 1))`. Rewrite using `[← hstep, ← mul_assoc, show h * PiJ m E u = 1 from hh, one_mul]`. Rewrite using `[e1]`.

Use `B.mul_mem hhB (B.mul_mem (B.algebraMap_mem _) ?_)` and prove the remaining obligations. Use `Subalgebra.list_prod_mem _ ?_` and prove the remaining obligations. Introduce `a ha`. Take `⟨j, rfl⟩` from `List.mem_ofFn.mp ha`. Conclude with `B.add_mem (B.algebraMap_mem _) (hxB j)`.

Establish `hinf : {u : ℂ | ∀ j : Fin m, ∀ c ∈ L' j, u + c ≠ 0}.Infinite`. Use `Set.Infinite.mono ?_ (Finset.finite_toSet (Finset.univ.biUnion fun j => ((L' j).map (fun c => -c)).toFinset)).infinite_compl` and prove the remaining obligations. Introduce `u hu j c hc h`. Apply `hu` to reduce the goal to its premises. Rewrite using `[Finset.mem_coe, Finset.mem_biUnion]`.

Conclude with `⟨j, Finset.mem_univ _, List.mem_toFinset.mpr (List.mem_map.mpr ⟨c, hc, by linear_combination -h⟩)⟩`. Establish `hqA : ∀ u, qdet (tE Finset.univ E) u ∈ A` using `TF.qdet_mem _ A (fun a b => Algebra.subset_adjoin ⟨(), a, b, rfl⟩)`. Establish `hcoefmem : ∀ (K : Subalgebra ℂ (Module.End ℂ (TV n M (Fin m)))) (Su : Set ℂ), Su.Infinite → (∀ u ∈ Su, qdet (tE Finset.univ E) u ∈ K) → ∀ i ∈ Finset.range (n + 1), c i ∈ K`. Introduce `K Su hSu hK i hi`. Use `TF.coef (n + 1) (fun i => (Subalgebra.toSubmodule K).mkQ (c i)) Su hSu (by` as an intermediate fact.

Introduce `u hu`. Establish `h1` using `hK u hu`. Rewrite `h1` using `[hc u]`. Establish `h2 : (Subalgebra.toSubmodule K).mkQ (∑ i ∈ Finset.range (n + 1), u ^ i • c i) = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Conclude with `h1`. Simplify `h2) i hi` using `[map_sum, map_smul]`. Rewrite `this` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `this`. Establish `hcB : ∀ i ∈ Finset.range (n + 1), c i ∈ B` using `hcoefmem B _ hinf (fun u hu => hqB u hu)`.

Establish `hcA : ∀ i ∈ Finset.range (n + 1), c i ∈ A` using `hcoefmem A Set.univ Set.infinite_univ (fun u _ => hqA u)`. Set `p : Polynomial ℂ` to `∏ k : Fin n, (Polynomial.X + Polynomial.C ((l k : ℂ) + (((Finset.univ.filter fun q : Fin m => co q = k).card : ℕ) : ℂ)))`. Establish `hpdeg : p.natDegree < n + 1`. Use `Polynomial.natDegree_prod_le (Finset.univ : Finset (Fin n)) (fun k : Fin n => Polynomial.X + Polynomial.C ((l k : ℂ) + (((Finset.univ.filter fun q : Fin m => co q = k).card : ℕ) : ℂ)))` as an intermediate fact. Simplify using `only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this`.

Conclude with `lt_of_le_of_lt this (by omega)`. Establish `hpev : ∀ u : ℂ, (∏ k : Fin n, (u + (l k : ℂ) + (((Finset.univ.filter fun q : Fin m => co q = k).card : ℕ) : ℂ))) = ∑ i ∈ Finset.range (n + 1), p.coeff i * u ^ i`. Introduce `u`. Rewrite using `[← Polynomial.eval_eq_sum_range' hpdeg u]`. Simplify using `[p, Polynomial.eval_prod, add_assoc]`.

Take `⟨g, hgB, hg0, hgx, hgq⟩` from `hC n M E hE (fun k => (l k : ℂ)) hl ℓ hℓ hW top htop m co`. Take `⟨c0, hc0⟩` from `hCA n M E hE ℓ hW top htop m col b hmono htab`. Use `set φ := ℓ ∘ₗ (LinearMap.proj fun _ : Fin m => top) ∘ₗ g with hφ`. Use `set ρ := ℓ ∘ₗ cA col b with hρ`. Establish `hφc : ∀ i ∈ Finset.range (n + 1), φ ∘ₗ c i - p.coeff i • φ = 0`.

Use `TF.coef (n + 1) (fun i => φ ∘ₗ c i - p.coeff i • φ) Set.univ Set.infinite_univ ?_` and prove the remaining obligations. Introduce `u _`. Establish `h1` using `hgq u`. Rewrite `h1` using `[hc u, hpev u, hcs, Finset.sum_smul]`. Simplify using `only [LinearMap.comp_smul] at h1`.

Establish `h2` using `sub_eq_zero.mpr h1`. Rewrite `h2` using `[← Finset.sum_sub_distrib]`. Rewrite using `[← h2]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_sub, smul_smul, mul_comm]`.

Choose the witnesses or unpack the hypotheses as in `⟨d, hd0, hd⟩ : ∃ d : ℂ, d ≠ 0 ∧ φ ∘ₗ colD E col = d • φ := by`. Unfold `colD`. Apply `TF.eig_prod` to reduce the goal to its premises. Introduce `a ha`. Take `⟨j, rfl⟩` from `List.mem_ofFn.mp ha`.

Apply `TF.eig_prod` to reduce the goal to its premises. Introduce `a ha`. Take `⟨i, rfl⟩` from `List.mem_ofFn.mp ha`. Use `split_ifs with hij`. Use `⟨((l (co i) : ℂ) + (((Finset.univ.filter fun q : Fin m => q < i ∧ co q = co i).card : ℕ) : ℂ)) - ((l (co j) : ℂ) + (((Finset.univ.filter fun q : Fin m => q < j ∧ co q = co j).card : ℕ) : ℂ)) + 1, ?_, ?_⟩` and prove the remaining obligations.

Establish `h` using `hcol i j hij.1 hij.2`. Establish `hpos : (0 : ℤ) < (l (co i) + (((Finset.univ.filter fun q : Fin m => q < i ∧ co q = co i).card : ℕ) : ℤ)) - (l (co j) + (((Finset.univ.filter fun q : Fin m => q < j ∧ co q = co j).card : ℕ) : ℤ)) + 1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : ((((l (co i) + (((Finset.univ.filter fun q : Fin m => q < i ∧ co q = co i).card : ℕ) : ℤ)) - (l (co j) + (((Finset.univ.filter fun q : Fin m => q < j ∧ co q = co j).card : ℕ) : ℤ)) + 1 : ℤ)) : ℂ) ≠ 0`. Conclude with `hpos.ne'` after adjusting the coercions.

Move the coercions through the operations in `at h3`. Conclude with `h3`. Rewrite using `[LinearMap.comp_add, LinearMap.comp_sub, hgx i, hgx j, show φ ∘ₗ (1 : Module.End ℂ (TV n M (Fin m))) = φ from rfl] conv_rhs => rw [add_smul, sub_smul, one_smul]`. Conclude with `⟨1, one_ne_zero, by rw [one_smul]; rfl⟩`. Establish `hcolDB : colD E col ∈ B`.

Unfold `colD`. Use `Subalgebra.list_prod_mem _ ?_` and prove the remaining obligations. Introduce `a ha`. Take `⟨j, rfl⟩` from `List.mem_ofFn.mp ha`. Use `Subalgebra.list_prod_mem _ ?_` and prove the remaining obligations.

Introduce `a ha`. Take `⟨i, rfl⟩` from `List.mem_ofFn.mp ha`. Use `split_ifs`. Conclude with `B.add_mem (B.sub_mem (hxB i) (hxB j)) B.one_mem`. Conclude with `B.one_mem`.

Establish `hgc : ∀ v, g (colD E col v) = colD E col (g v)` using `fun v => LinearMap.congr_fun (hBcomm g hgB _ hcolDB).eq v`. Establish `key : c0 • (ρ ∘ₗ g) = d • φ`. Rewrite using `[← hd]`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun hc0 (g v)`.

Rewrite using `[hφ, hρ]`. Rewrite `h1` using `[hρ]`. Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply] at h1 ⊢`. Rewrite using `[hgc]`. Conclude with `h1.symm`.

Establish `hc0ne : c0 ≠ 0`. Introduce `h`. Apply `hg0` to reduce the goal to its premises. Rewrite `key` using `[h, zero_smul]`. Conclude with `(smul_eq_zero.mp key.symm).resolve_left hd0`.

Establish `hρg : ρ ∘ₗ g = (c0⁻¹ * d) • φ`. Rewrite using `[mul_smul, ← key, smul_smul, inv_mul_cancel₀ hc0ne, one_smul]`. Use `set Tm : ℕ → Module.End ℂ (TV n M (Fin m)) := fun i => if i < n + 1 then c i - algebraMap ℂ _ (p.coeff i) else 0 with hTm`. Establish `hTmi : ∀ i ∈ Finset.range (n + 1), Tm i = c i - algebraMap ℂ _ (p.coeff i)`. Introduce `i hi`.

Use `show (if i < n + 1 then c i - algebraMap ℂ _ (p.coeff i) else 0) = _`. Conclude with `if_pos (Finset.mem_range.mp hi)`. Establish `hTmB : ∀ i, Tm i ∈ B ∧ Tm i ∈ A`. Introduce `i`. Distinguish the cases in `h : i < n + 1`.

Rewrite using `[hTmi i (Finset.mem_range.mpr h)]`. Conclude with `⟨B.sub_mem (hcB i (Finset.mem_range.mpr h)) (B.algebraMap_mem _), A.sub_mem (hcA i (Finset.mem_range.mpr h)) (A.algebraMap_mem _)⟩`. Establish `e : Tm i = 0` using `if_neg h`. Rewrite using `[e]`. Conclude with `⟨B.zero_mem, A.zero_mem⟩`.

Establish `hρgT : ∀ i ∈ Finset.range (n + 1), ρ ∘ₗ (g ∘ₗ Tm i) = 0`. Introduce `i hi`. Rewrite using `[← LinearMap.comp_assoc, hρg, LinearMap.smul_comp, hTmi i hi, LinearMap.comp_sub, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul, show φ ∘ₗ (1 : Module.End ℂ (TV n M (Fin m))) = φ from rfl, hφc i hi, smul_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨v0, hv0⟩ : ∃ v, φ v ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hg0 (LinearMap.ext h)`. Use `haveI hQfin : FiniteDimensional ℂ (Subalgebra.toSubmodule (B ⊓ A)) := Submodule.finiteDimensional_of_le (S₂ := Subalgebra.toSubmodule B) (fun x hx => hx.1)`. Take `⟨z, hzZ, hz0, hzT⟩` from `TF.common_ker (fun i => TF.rc (Tm i)) (fun i j => TF.rc_comm _ _ (hBcomm _ (hTmB i).1 _ (hTmB j).1)) (TF.ev (g v0)) (Finset.range (n + 1)) (Submodule.map (TF.lc ρ) (Subalgebra.toSubmodule (B ⊓ A))) inferInstance (by`. Introduce `i _ z hz`.

Take `⟨S, hS, rfl⟩` from `Submodule.mem_map.mp hz`. Conclude with `Submodule.mem_map.mpr ⟨S * Tm i, (B ⊓ A).mul_mem hS ⟨(hTmB i).1, (hTmB i).2⟩, rfl⟩)`. Use the proof step `(by`. Introduce `i hi z hz`. Take `⟨S, hS, rfl⟩` from `Submodule.mem_map.mp hz`.

Use `show ρ (S (Tm i (g v0))) = 0`. Establish `hSB : S ∈ B` using `hS.1`. Establish `h1 : S * (Tm i * g) = g * (Tm i * S)`. Rewrite using `[← mul_assoc, (hBcomm _ (B.mul_mem hSB (hTmB i).1) g hgB).eq, (hBcomm S hSB _ (hTmB i).1).eq]`. Establish `h2` using `LinearMap.congr_fun h1 v0`.

Simplify using `only [Module.End.mul_apply] at h2`. Rewrite using `[h2]`. Establish `h3` using `LinearMap.congr_fun (hρgT i hi) (S v0)`. Simplify using `using h3)`. Use the proof step `⟨TF.lc ρ 1, Submodule.mem_map.mpr ⟨1, (B ⊓ A).one_mem, rfl⟩, by show ρ (g v0) ≠ 0`.

Establish `h1` using `LinearMap.congr_fun hρg v0`. Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h1`. Rewrite using `[h1]`. Conclude with `mul_ne_zero (mul_ne_zero (inv_ne_zero hc0ne) hd0) hv0⟩`. Take `⟨S, hS, rfl⟩` from `Submodule.mem_map.mp hzZ`.

Use `⟨S, hS.2, hz0, fun u => ?_⟩` and prove the remaining obligations. Use `show (ρ ∘ₗ S) ∘ₗ qdet (tE Finset.univ E) u = _ • (ρ ∘ₗ S)`. Establish `hψ : ∀ i ∈ Finset.range (n + 1), (ρ ∘ₗ S) ∘ₗ c i = p.coeff i • (ρ ∘ₗ S)`. Introduce `i hi`. Establish `h3 : (ρ ∘ₗ S) ∘ₗ Tm i = 0` using `hzT i hi`.

Rewrite `h3` using `[hTmi i hi, LinearMap.comp_sub, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul, sub_eq_zero]`. Conclude with `h3`. Rewrite using `[hc u, hpev u, hcs, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_smul, hψ i hi, smul_smul, mul_comm]`.
-/
theorem transFin_of : TensorGl → JMComm → StepFormula → QdetFacts → Spectrum → Chain → ColAnti → TransFin := by
  intro hT hJ hS hQ hSp hC hCA
  intro n M _ _ E hE l hl ℓ hℓ hW hn m col b co hmono htab hcol
  let top : Fin n := ⟨n - 1, by omega⟩
  have htop : (top : ℕ) + 1 = n := by
    show n - 1 + 1 = n
    omega
  have hE' : GlRel (tE (Finset.univ : Finset (Fin m)) E) := (hT n M (Fin m) E hE Finset.univ).1
  obtain ⟨c, hc⟩ := (hQ n (TV n M (Fin m)) (tE (Finset.univ : Finset (Fin m)) E) hE').2.1
  set B : Subalgebra ℂ (Module.End ℂ (TV n M (Fin m))) :=
    Algebra.adjoin ℂ (Set.range fun j : Fin m => xJ E j) with hB
  set A := envAlg fun _ : Unit => tE (Finset.univ : Finset (Fin m)) E with hA
  have hxcomm : ∀ i j : Fin m, Commute (xJ E i) (xJ E j) := (hJ n M E hE m).1
  have hxB : ∀ j, xJ E j ∈ B := fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, Commute x y := by
    intro x hx y hy
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy ?_
    rintro _ ⟨j, rfl⟩
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx ?_).symm
    rintro _ ⟨i, rfl⟩
    exact hxcomm j i
  have hcs : ∀ (f : TV n M (Fin m) →ₗ[ℂ] ℂ) (h : ℕ → Module.End ℂ (TV n M (Fin m))),
      f ∘ₗ (∑ i ∈ Finset.range (n + 1), h i) = ∑ i ∈ Finset.range (n + 1), f ∘ₗ h i := by
    intro f h
    refine LinearMap.ext fun v => ?_
    simp
  set N : ℤ := ∑ k, |l k| with hN
  have hlN : ∀ k, 0 ≤ l k + N := by
    intro k
    have h1 : |l k| ≤ N :=
      Finset.single_le_sum (f := fun k => |l k|) (fun k _ => abs_nonneg _) (Finset.mem_univ k)
    have h2 := neg_abs_le (l k)
    linarith
  have hsp := hSp n M E hE (fun k => (l k : ℂ)) (-(N : ℂ)) hl (fun k => ⟨(l k + N).toNat, by
      rw [show (((l k + N).toNat : ℕ) : ℂ) = ((l k + N : ℤ) : ℂ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (hlN k)]]
      push_cast
      ring⟩) m
  choose L hL using hsp.2
  let L' : Fin m → List ℂ := fun j => (L j).map (fun r : ℕ => -(N : ℂ) + r)
  have hL' : ∀ j, (List.map (fun c => xJ E j - algebraMap ℂ _ c) (L' j)).prod = 0 := by
    intro j
    rw [List.map_map]
    exact hL j
  haveI hBfin : FiniteDimensional ℂ (Subalgebra.toSubmodule B) :=
    TF.fin_adjoin (fun j : Fin m => xJ E j) hxcomm (fun j => ⟨L' j, hL' j⟩)
  have hlift : ∀ u : ℂ, (lift (qdet E u) : Module.End ℂ (TV n M (Fin m))) =
      algebraMap ℂ _ (∏ k, (u + (l k : ℂ))) := by
    intro u
    rw [hl u]
    exact TF.lift_alg _
  have hqB : ∀ u : ℂ, (∀ j : Fin m, ∀ c ∈ L' j, u + c ≠ 0) → qdet (tE Finset.univ E) u ∈ B := by
    intro u hu
    obtain ⟨h, hhB, hh⟩ := TF.left_inv_prod B.toSubring
      (List.ofFn fun j : Fin m => algebraMap ℂ (Module.End ℂ (TV n M (Fin m))) u + xJ E j) (by
        intro a ha
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
        exact TF.inv_of_alg B (xJ E j) (hxB j) u (L' j) (hL' j) (hu j))
    have hstep := hS n M E hE m u
    rw [hlift] at hstep
    have e1 : qdet (tE Finset.univ E) u =
        h * (algebraMap ℂ _ (∏ k, (u + (l k : ℂ))) * PiJ m E (u + 1)) := by
      rw [← hstep, ← mul_assoc, show h * PiJ m E u = 1 from hh, one_mul]
    rw [e1]
    refine B.mul_mem hhB (B.mul_mem (B.algebraMap_mem _) ?_)
    refine Subalgebra.list_prod_mem _ ?_
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact B.add_mem (B.algebraMap_mem _) (hxB j)
  have hinf : {u : ℂ | ∀ j : Fin m, ∀ c ∈ L' j, u + c ≠ 0}.Infinite := by
    refine Set.Infinite.mono ?_
      (Finset.finite_toSet (Finset.univ.biUnion fun j => ((L' j).map (fun c => -c)).toFinset)).infinite_compl
    intro u hu j c hc h
    apply hu
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨j, Finset.mem_univ _, List.mem_toFinset.mpr (List.mem_map.mpr ⟨c, hc, by linear_combination -h⟩)⟩
  have hqA : ∀ u, qdet (tE Finset.univ E) u ∈ A :=
    TF.qdet_mem _ A (fun a b => Algebra.subset_adjoin ⟨(), a, b, rfl⟩)
  have hcoefmem : ∀ (K : Subalgebra ℂ (Module.End ℂ (TV n M (Fin m)))) (Su : Set ℂ), Su.Infinite →
      (∀ u ∈ Su, qdet (tE Finset.univ E) u ∈ K) → ∀ i ∈ Finset.range (n + 1), c i ∈ K := by
    intro K Su hSu hK i hi
    have := TF.coef (n + 1) (fun i => (Subalgebra.toSubmodule K).mkQ (c i)) Su hSu (by
      intro u hu
      have h1 := hK u hu
      rw [hc u] at h1
      have h2 : (Subalgebra.toSubmodule K).mkQ (∑ i ∈ Finset.range (n + 1), u ^ i • c i) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact h1
      simpa [map_sum, map_smul] using h2) i hi
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  have hcB : ∀ i ∈ Finset.range (n + 1), c i ∈ B := hcoefmem B _ hinf (fun u hu => hqB u hu)
  have hcA : ∀ i ∈ Finset.range (n + 1), c i ∈ A :=
    hcoefmem A Set.univ Set.infinite_univ (fun u _ => hqA u)
  let p : Polynomial ℂ := ∏ k : Fin n,
    (Polynomial.X + Polynomial.C ((l k : ℂ) + (((Finset.univ.filter fun q : Fin m => co q = k).card : ℕ) : ℂ)))
  have hpdeg : p.natDegree < n + 1 := by
    have := Polynomial.natDegree_prod_le (Finset.univ : Finset (Fin n)) (fun k : Fin n =>
      Polynomial.X + Polynomial.C ((l k : ℂ) + (((Finset.univ.filter fun q : Fin m => co q = k).card : ℕ) : ℂ)))
    simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at this
    exact lt_of_le_of_lt this (by omega)
  have hpev : ∀ u : ℂ, (∏ k : Fin n, (u + (l k : ℂ) + (((Finset.univ.filter fun q : Fin m => co q = k).card : ℕ) : ℂ))) =
      ∑ i ∈ Finset.range (n + 1), p.coeff i * u ^ i := by
    intro u
    rw [← Polynomial.eval_eq_sum_range' hpdeg u]
    simp [p, Polynomial.eval_prod, add_assoc]
  obtain ⟨g, hgB, hg0, hgx, hgq⟩ := hC n M E hE (fun k => (l k : ℂ)) hl ℓ hℓ hW top htop m co
  obtain ⟨c0, hc0⟩ := hCA n M E hE ℓ hW top htop m col b hmono htab
  set φ := ℓ ∘ₗ (LinearMap.proj fun _ : Fin m => top) ∘ₗ g with hφ
  set ρ := ℓ ∘ₗ cA col b with hρ
  have hφc : ∀ i ∈ Finset.range (n + 1), φ ∘ₗ c i - p.coeff i • φ = 0 := by
    refine TF.coef (n + 1) (fun i => φ ∘ₗ c i - p.coeff i • φ) Set.univ Set.infinite_univ ?_
    intro u _
    have h1 := hgq u
    rw [hc u, hpev u, hcs, Finset.sum_smul] at h1
    simp only [LinearMap.comp_smul] at h1
    have h2 := sub_eq_zero.mpr h1
    rw [← Finset.sum_sub_distrib] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_sub, smul_smul, mul_comm]
  obtain ⟨d, hd0, hd⟩ : ∃ d : ℂ, d ≠ 0 ∧ φ ∘ₗ colD E col = d • φ := by
    unfold colD
    apply TF.eig_prod
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    apply TF.eig_prod
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    split_ifs with hij
    · refine ⟨((l (co i) : ℂ) + (((Finset.univ.filter fun q : Fin m => q < i ∧ co q = co i).card : ℕ) : ℂ)) -
          ((l (co j) : ℂ) + (((Finset.univ.filter fun q : Fin m => q < j ∧ co q = co j).card : ℕ) : ℂ)) + 1, ?_, ?_⟩
      · have h := hcol i j hij.1 hij.2
        have hpos : (0 : ℤ) < (l (co i) + (((Finset.univ.filter fun q : Fin m => q < i ∧ co q = co i).card : ℕ) : ℤ)) -
            (l (co j) + (((Finset.univ.filter fun q : Fin m => q < j ∧ co q = co j).card : ℕ) : ℤ)) + 1 := by
          linarith
        have h3 : ((((l (co i) + (((Finset.univ.filter fun q : Fin m => q < i ∧ co q = co i).card : ℕ) : ℤ)) -
            (l (co j) + (((Finset.univ.filter fun q : Fin m => q < j ∧ co q = co j).card : ℕ) : ℤ)) + 1 : ℤ)) : ℂ) ≠ 0 := by
          exact_mod_cast hpos.ne'
        push_cast at h3
        exact h3
      · rw [LinearMap.comp_add, LinearMap.comp_sub, hgx i, hgx j,
          show φ ∘ₗ (1 : Module.End ℂ (TV n M (Fin m))) = φ from rfl]
        conv_rhs => rw [add_smul, sub_smul, one_smul]
    · exact ⟨1, one_ne_zero, by rw [one_smul]; rfl⟩
  have hcolDB : colD E col ∈ B := by
    unfold colD
    refine Subalgebra.list_prod_mem _ ?_
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    refine Subalgebra.list_prod_mem _ ?_
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    split_ifs
    · exact B.add_mem (B.sub_mem (hxB i) (hxB j)) B.one_mem
    · exact B.one_mem
  have hgc : ∀ v, g (colD E col v) = colD E col (g v) := fun v =>
    LinearMap.congr_fun (hBcomm g hgB _ hcolDB).eq v
  have key : c0 • (ρ ∘ₗ g) = d • φ := by
    rw [← hd]
    refine LinearMap.ext fun v => ?_
    have h1 := LinearMap.congr_fun hc0 (g v)
    rw [hφ, hρ]
    rw [hρ] at h1
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h1 ⊢
    rw [hgc]
    exact h1.symm
  have hc0ne : c0 ≠ 0 := by
    intro h
    apply hg0
    rw [h, zero_smul] at key
    exact (smul_eq_zero.mp key.symm).resolve_left hd0
  have hρg : ρ ∘ₗ g = (c0⁻¹ * d) • φ := by
    rw [mul_smul, ← key, smul_smul, inv_mul_cancel₀ hc0ne, one_smul]
  set Tm : ℕ → Module.End ℂ (TV n M (Fin m)) :=
    fun i => if i < n + 1 then c i - algebraMap ℂ _ (p.coeff i) else 0 with hTm
  have hTmi : ∀ i ∈ Finset.range (n + 1), Tm i = c i - algebraMap ℂ _ (p.coeff i) := by
    intro i hi
    show (if i < n + 1 then c i - algebraMap ℂ _ (p.coeff i) else 0) = _
    exact if_pos (Finset.mem_range.mp hi)
  have hTmB : ∀ i, Tm i ∈ B ∧ Tm i ∈ A := by
    intro i
    by_cases h : i < n + 1
    · rw [hTmi i (Finset.mem_range.mpr h)]
      exact ⟨B.sub_mem (hcB i (Finset.mem_range.mpr h)) (B.algebraMap_mem _),
        A.sub_mem (hcA i (Finset.mem_range.mpr h)) (A.algebraMap_mem _)⟩
    · have e : Tm i = 0 := if_neg h
      rw [e]
      exact ⟨B.zero_mem, A.zero_mem⟩
  have hρgT : ∀ i ∈ Finset.range (n + 1), ρ ∘ₗ (g ∘ₗ Tm i) = 0 := by
    intro i hi
    rw [← LinearMap.comp_assoc, hρg, LinearMap.smul_comp, hTmi i hi, LinearMap.comp_sub,
      Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul,
      show φ ∘ₗ (1 : Module.End ℂ (TV n M (Fin m))) = φ from rfl, hφc i hi, smul_zero]
  obtain ⟨v0, hv0⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hg0 (LinearMap.ext h)
  haveI hQfin : FiniteDimensional ℂ (Subalgebra.toSubmodule (B ⊓ A)) :=
    Submodule.finiteDimensional_of_le (S₂ := Subalgebra.toSubmodule B) (fun x hx => hx.1)
  obtain ⟨z, hzZ, hz0, hzT⟩ := TF.common_ker (fun i => TF.rc (Tm i))
    (fun i j => TF.rc_comm _ _ (hBcomm _ (hTmB i).1 _ (hTmB j).1)) (TF.ev (g v0))
    (Finset.range (n + 1)) (Submodule.map (TF.lc ρ) (Subalgebra.toSubmodule (B ⊓ A))) inferInstance
    (by
      intro i _ z hz
      obtain ⟨S, hS, rfl⟩ := Submodule.mem_map.mp hz
      exact Submodule.mem_map.mpr ⟨S * Tm i, (B ⊓ A).mul_mem hS ⟨(hTmB i).1, (hTmB i).2⟩, rfl⟩)
    (by
      intro i hi z hz
      obtain ⟨S, hS, rfl⟩ := Submodule.mem_map.mp hz
      show ρ (S (Tm i (g v0))) = 0
      have hSB : S ∈ B := hS.1
      have h1 : S * (Tm i * g) = g * (Tm i * S) := by
        rw [← mul_assoc, (hBcomm _ (B.mul_mem hSB (hTmB i).1) g hgB).eq, (hBcomm S hSB _ (hTmB i).1).eq]
      have h2 := LinearMap.congr_fun h1 v0
      simp only [Module.End.mul_apply] at h2
      rw [h2]
      have h3 := LinearMap.congr_fun (hρgT i hi) (S v0)
      simpa using h3)
    ⟨TF.lc ρ 1, Submodule.mem_map.mpr ⟨1, (B ⊓ A).one_mem, rfl⟩, by
      show ρ (g v0) ≠ 0
      have h1 := LinearMap.congr_fun hρg v0
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h1
      rw [h1]
      exact mul_ne_zero (mul_ne_zero (inv_ne_zero hc0ne) hd0) hv0⟩
  obtain ⟨S, hS, rfl⟩ := Submodule.mem_map.mp hzZ
  refine ⟨S, hS.2, hz0, fun u => ?_⟩
  show (ρ ∘ₗ S) ∘ₗ qdet (tE Finset.univ E) u = _ • (ρ ∘ₗ S)
  have hψ : ∀ i ∈ Finset.range (n + 1), (ρ ∘ₗ S) ∘ₗ c i = p.coeff i • (ρ ∘ₗ S) := by
    intro i hi
    have h3 : (ρ ∘ₗ S) ∘ₗ Tm i = 0 := hzT i hi
    rw [hTmi i hi, LinearMap.comp_sub, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul,
      sub_eq_zero] at h3
    exact h3
  rw [hc u, hpev u, hcs, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [LinearMap.comp_smul, hψ i hi, smul_smul, mul_comm]

end PositivityTheory.Rg.Cz
