import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClrHolds

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2
open scoped Classical

namespace UpperTheory.Gal.W2.RootSumScaling

open UpperTheory.Gal.Schur

variable {F : Type} [Field F] [NumberField F]

end UpperTheory.Gal.W2.RootSumScaling

/- English proof (translation)
Unfold `UpperTheory.Gal.Schur.sch GroundTheory.Heights₂.Heights.RestTerms.schur`. Rewrite using `[← MvPolynomial.aeval_rename, AlgHom.map_det]`. Use `congr 2`. Use extensionality with `i j`. Simplify using `[GroundTheory.Heights₂.Heights.RestTerms.Schur.rename_completeSymmetric]`.
-/
private theorem sch_comp_perm {n : ℕ} (lam : Fin n → ℕ) (g : Fin n → ℂ) (e : Equiv.Perm (Fin n)) :
    UpperTheory.Gal.Schur.sch lam (g ∘ e) = UpperTheory.Gal.Schur.sch lam g := by
  unfold UpperTheory.Gal.Schur.sch GroundTheory.Heights₂.Heights.RestTerms.schur
  rw [← MvPolynomial.aeval_rename, AlgHom.map_det]
  congr 2
  ext i j
  simp [GroundTheory.Heights₂.Heights.RestTerms.Schur.rename_completeSymmetric]

/- English proof (translation)
Use `choose f hf using hsub`. Establish `hinj : Function.Injective f`. Introduce `j j' h`. Apply `ha` to reduce the goal to its premises. Rewrite using `[← hf j, ← hf j', h]`.

Use `⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Simplify using `[hf]`.
-/
private theorem exists_perm_eq_comp_of_injective_of_surj {n : ℕ} (a b : Fin n → ℂ) (ha : Function.Injective a)
    (hsub : ∀ j, ∃ k, b k = a j) : ∃ e : Equiv.Perm (Fin n), a = b ∘ e := by
  choose f hf using hsub
  have hinj : Function.Injective f := by
    intro j j' h
    apply ha
    rw [← hf j, ← hf j', h]
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_⟩
  funext j
  simp [hf]

/- English proof (translation)
Unfold `UpperTheory.Gal.Schur.detOne`. Conclude with `(Finset.mul_prod_erase _ (fun k => 1 - x * v k) (Finset.mem_univ i)).symm`.
-/
private theorem detOne_eq_mul_prod_erase {n : ℕ} (x : ℂ) (v : Fin n → ℂ) (i : Fin n) :
    UpperTheory.Gal.Schur.detOne x v = (1 - x * v i) * ∏ k ∈ Finset.univ.erase i, (1 - x * v k) := by
  unfold UpperTheory.Gal.Schur.detOne
  exact (Finset.mul_prod_erase _ (fun k => 1 - x * v k) (Finset.mem_univ i)).symm

/- English proof (translation)
Rewrite using `[← Multiset.map_erase a ha, Multiset.map_map, ← Finset.erase_val]`. Both sides reduce to the same expression.
-/
private theorem prod_map_erase_eq_prod_univ_erase {n : ℕ} (a : Fin n → ℂ) (ha : Function.Injective a) (i : Fin n)
    (f : ℂ → ℂ) :
    (Multiset.map f ((Multiset.map a Finset.univ.val).erase (a i))).prod =
      ∏ k ∈ Finset.univ.erase i, f (a k) := by
  rw [← Multiset.map_erase a ha, Multiset.map_map, ← Finset.erase_val]
  rfl

open UpperTheory.Gal.W2.RootSumScaling in
/- English proof (translation)
Introduce `F _ _ n t₀ ε lam m hconj hlam`. Take `⟨k₀, hk₀⟩` from `UpperTheory.Gal.Schur.FibreSum_holds F ℂ n lam`. Use `⟨k₀, fun k hk => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hsum⟩` from `hk₀ k hk 2 two_ne_zero ∅`. Use `⟨c, fun α hα s => ⟨(hc α hα s).1, (hc α hα s).2.1⟩, ?_⟩` and prove the remaining obligations.

Introduce `χ r hsep hr y`. Use `set t₁ := ComplexEmbedding.conjugate t₀ with ht₁`. Establish `hinj : ∀ τ, Function.Injective (r τ)`. Introduce `τ a b hab`. Establish `hnd : (Multiset.map (r τ) Finset.univ.val).Nodup`.

Rewrite using `[← hr τ]`. Conclude with `Polynomial.nodup_roots hsep.map`. Conclude with `Multiset.inj_on_of_nodup_map hnd a (Finset.mem_univ a) b (Finset.mem_univ b) hab`. Establish `hmap1 : χ.map t₁ = (χ.map t₀).map (starRingEnd ℂ)`. Rewrite using `[Polynomial.map_map]`.

Use `congr 1`. Establish `hroot : ∀ j, ∃ k, r t₁ k = starRingEnd ℂ (r t₀ j)`. Introduce `j`. Establish `hmem : r t₀ j ∈ (χ.map t₀).roots`. Express the relevant statement in the definitionally equal form `r t₀ j ∈ rts χ t₀`.

Rewrite using `[hr t₀]`. Conclude with `Multiset.mem_map_of_mem _ (Finset.mem_univ j)`. Establish `hne : χ.map t₁ ≠ 0` using `Polynomial.map_ne_zero hsep.ne_zero`. Establish `hmem' : starRingEnd ℂ (r t₀ j) ∈ rts χ t₁`. Express the relevant statement in the definitionally equal form `_ ∈ (χ.map t₁).roots`.

Rewrite using `[Polynomial.mem_roots hne, hmap1]`. Conclude with `(Polynomial.isRoot_of_mem_roots hmem).map`. Rewrite `hmem'` using `[hr t₁]`. Take `⟨k, -, hk⟩` from `Multiset.mem_map.mp hmem'`. Conclude with `⟨k, hk⟩`.

Take `⟨e, he⟩` from `exists_perm_eq_comp_of_injective_of_surj (fun j => starRingEnd ℂ (r t₀ j)) (r t₁) (fun a b h => hinj t₀ ((starRingEnd ℂ).injective h)) hroot`. Establish `h01 : t₀ ≠ t₁` using `fun h => hconj h.symm`. Use `set g : (F →+* ℂ) → Fin n → ℂ := fun τ => if τ = t₁ then (fun j => starRingEnd ℂ (r t₀ j)) else r τ with hgdef`. Establish `hg0 : g t₀ = r t₀` using `by simp [hgdef, h01]`. Establish `hg1 : g t₁ = fun j => starRingEnd ℂ (r t₀ j)` using `by simp [hgdef]`.

Establish `hgτ : ∀ τ, τ ≠ t₁ → g τ = r τ` using `fun τ h => by simp [hgdef, h]`. Establish `hunit : ∀ i j : Fin n, j ≠ i → IsUnit (g t₀ j - g t₀ i)`. Introduce `i j hji`. Rewrite using `[hg0]`. Conclude with `(sub_ne_zero.mpr (fun h => hji (hinj t₀ h))).isUnit`.

Establish `key` using `(hsum ℂ t₀ t₁ h01 ε m g y).1 hlam hunit`. Establish `hprod : ∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (g τ) = ∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (r τ)`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : τ = t₁`. Rewrite using `[h, hg1, he, sch_comp_perm]`.

Rewrite using `[hgτ τ h]`. Rewrite using `[← hprod, ← key]`. Use `Finsupp.sum_congr fun α _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul]`. Use `congr 1`.

Rewrite using `[hr t₀, Multiset.map_map]`. Use `(Finset.sum_congr rfl fun i _ => ?_ : ∑ i, locW t₀ ε α y χ (r t₀ i) = _)` and prove the remaining obligations. Establish `hB : ∀ f : ℂ → ℂ, (Multiset.map f ((rts χ t₀).erase (r t₀ i))).prod = ∏ k ∈ Finset.univ.erase i, f (r t₀ k)` using `fun f => by`. Rewrite using `[hr t₀]`. Conclude with `prod_map_erase_eq_prod_univ_erase _ (hinj t₀) i f`.

Unfold `locW`. Rewrite using `[mul_comm, Finset.prod_comm]`. Use `congr 1`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `hx0 : (algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₀ (α s)) = t₀ (α s : F)` using `rfl`.

Establish `hx1 : (algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₁ (α s)) = starRingEnd ℂ (t₀ (α s : F))` using `ComplexEmbedding.conjugate_coe_eq t₀ _`. Establish `hA : UpperTheory.Gal.Schur.detOne ((algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₀ (α s))) (UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₀) = (1 - t₀ (α s : F) * (y * r t₀ i)) * ∏ k ∈ Finset.univ.erase i, (1 - t₀ (α s : F) * r t₀ k)`. Rewrite using `[detOne_eq_mul_prod_erase _ _ i, hx0]`. Establish `htw : UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₀ = UpperTheory.Gal.Schur.scaleAt y i (r t₀)`. Simplify using `[UpperTheory.Gal.Schur.twist, hg0]`.

Rewrite using `[htw]`. Use `congr 1`. Simplify using `[UpperTheory.Gal.Schur.scaleAt]`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Simplify using `[UpperTheory.Gal.Schur.scaleAt, Finset.ne_of_mem_erase hk]`.

Establish `hC : UpperTheory.Gal.Schur.detOne ((algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₁ (α s))) (UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₁) = (1 - starRingEnd ℂ (t₀ (α s : F)) * starRingEnd ℂ (r t₀ i)) * ∏ k ∈ Finset.univ.erase i, (1 - starRingEnd ℂ (t₀ (α s : F)) * (y * starRingEn …`. Rewrite using `[detOne_eq_mul_prod_erase _ _ i, hx1]`. Establish `htw : UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₁ = UpperTheory.Gal.Schur.scaleOff y i (fun j => starRingEnd ℂ (r t₀ j))`. Simplify using `[UpperTheory.Gal.Schur.twist, hg1, h01.symm]`. Rewrite using `[htw]`.

Use `congr 1`. Simplify using `[UpperTheory.Gal.Schur.scaleOff]`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Simplify using `[UpperTheory.Gal.Schur.scaleOff, Finset.ne_of_mem_erase hk]`. Establish `hE : ∀ τ ∈ (Finset.univ.erase t₀).erase t₁, (Multiset.map (fun z => 1 - τ (α s : F) * (y ^ ε τ * z)) (rts χ τ)).prod = UpperTheory.Gal.Schur.detOne ((algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO τ (α s))) (UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g τ)`.

Introduce `τ hτ`. Establish `hτ1` using `Finset.ne_of_mem_erase hτ`. Establish `hτ0` using `Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hτ)`. Rewrite using `[hr τ, Multiset.map_map]`. Establish `htw : UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g τ = fun k => y ^ ε τ * r τ k`.

Simplify using `[UpperTheory.Gal.Schur.twist, hτ0, hτ1, hgτ τ hτ1]`. Rewrite using `[htw]`. Both sides reduce to the same expression. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ t₀), ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ t₁⟩), hA, hC, ← Finset.prod_congr rfl hE]`. Unfold `fibW`.

Rewrite using `[hB, hB]`. Expand and normalize the polynomial expressions, which then agree. Unfold `ballW`. Rewrite using `[hB, hg0]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Ring.inverse_eq_inv', div_eq_mul_inv]`.
-/
theorem UpperTheory.Gal.W2.rootSumW_of :
    UpperTheory.Gal.W2.RootSumW := by
  intro F _ _ n t₀ ε lam m hconj hlam
  obtain ⟨k₀, hk₀⟩ := UpperTheory.Gal.Schur.FibreSum_holds F ℂ n lam
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨c, hc, hsum⟩ := hk₀ k hk 2 two_ne_zero ∅
  refine ⟨c, fun α hα s => ⟨(hc α hα s).1, (hc α hα s).2.1⟩, ?_⟩
  intro χ r hsep hr y
  set t₁ := ComplexEmbedding.conjugate t₀ with ht₁
  have hinj : ∀ τ, Function.Injective (r τ) := by
    intro τ a b hab
    have hnd : (Multiset.map (r τ) Finset.univ.val).Nodup := by
      rw [← hr τ]
      exact Polynomial.nodup_roots hsep.map
    exact Multiset.inj_on_of_nodup_map hnd a (Finset.mem_univ a) b (Finset.mem_univ b) hab
  have hmap1 : χ.map t₁ = (χ.map t₀).map (starRingEnd ℂ) := by
    rw [Polynomial.map_map]
    congr 1
  have hroot : ∀ j, ∃ k, r t₁ k = starRingEnd ℂ (r t₀ j) := by
    intro j
    have hmem : r t₀ j ∈ (χ.map t₀).roots := by
      change r t₀ j ∈ rts χ t₀
      rw [hr t₀]
      exact Multiset.mem_map_of_mem _ (Finset.mem_univ j)
    have hne : χ.map t₁ ≠ 0 := Polynomial.map_ne_zero hsep.ne_zero
    have hmem' : starRingEnd ℂ (r t₀ j) ∈ rts χ t₁ := by
      change _ ∈ (χ.map t₁).roots
      rw [Polynomial.mem_roots hne, hmap1]
      exact (Polynomial.isRoot_of_mem_roots hmem).map
    rw [hr t₁] at hmem'
    obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp hmem'
    exact ⟨k, hk⟩
  obtain ⟨e, he⟩ := exists_perm_eq_comp_of_injective_of_surj (fun j => starRingEnd ℂ (r t₀ j)) (r t₁)
    (fun a b h => hinj t₀ ((starRingEnd ℂ).injective h)) hroot
  have h01 : t₀ ≠ t₁ := fun h => hconj h.symm
  set g : (F →+* ℂ) → Fin n → ℂ :=
    fun τ => if τ = t₁ then (fun j => starRingEnd ℂ (r t₀ j)) else r τ with hgdef
  have hg0 : g t₀ = r t₀ := by simp [hgdef, h01]
  have hg1 : g t₁ = fun j => starRingEnd ℂ (r t₀ j) := by simp [hgdef]
  have hgτ : ∀ τ, τ ≠ t₁ → g τ = r τ := fun τ h => by simp [hgdef, h]
  have hunit : ∀ i j : Fin n, j ≠ i → IsUnit (g t₀ j - g t₀ i) := by
    intro i j hji
    rw [hg0]
    exact (sub_ne_zero.mpr (fun h => hji (hinj t₀ h))).isUnit
  have key := (hsum ℂ t₀ t₁ h01 ε m g y).1 hlam hunit
  have hprod : ∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (g τ) =
      ∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (r τ) := by
    refine Finset.prod_congr rfl fun τ _ => ?_
    by_cases h : τ = t₁
    · rw [h, hg1, he, sch_comp_perm]
    · rw [hgτ τ h]
  rw [← hprod, ← key]
  refine Finsupp.sum_congr fun α _ => ?_
  rw [smul_eq_mul]
  congr 1
  rw [hr t₀, Multiset.map_map]
  refine (Finset.sum_congr rfl fun i _ => ?_ :
    ∑ i, locW t₀ ε α y χ (r t₀ i) = _)
  have hB : ∀ f : ℂ → ℂ, (Multiset.map f ((rts χ t₀).erase (r t₀ i))).prod =
      ∏ k ∈ Finset.univ.erase i, f (r t₀ k) := fun f => by
    rw [hr t₀]
    exact prod_map_erase_eq_prod_univ_erase _ (hinj t₀) i f
  unfold locW
  rw [mul_comm, Finset.prod_comm]
  congr 1
  · refine Finset.prod_congr rfl fun s _ => ?_
    have hx0 : (algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₀ (α s)) = t₀ (α s : F) := rfl
    have hx1 : (algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₁ (α s)) = starRingEnd ℂ (t₀ (α s : F)) :=
      ComplexEmbedding.conjugate_coe_eq t₀ _
    have hA : UpperTheory.Gal.Schur.detOne ((algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₀ (α s)))
        (UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₀) =
        (1 - t₀ (α s : F) * (y * r t₀ i)) * ∏ k ∈ Finset.univ.erase i, (1 - t₀ (α s : F) * r t₀ k) := by
      rw [detOne_eq_mul_prod_erase _ _ i, hx0]
      have htw : UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₀ = UpperTheory.Gal.Schur.scaleAt y i (r t₀) := by
        simp [UpperTheory.Gal.Schur.twist, hg0]
      rw [htw]
      congr 1
      · simp [UpperTheory.Gal.Schur.scaleAt]
      · refine Finset.prod_congr rfl fun k hk => ?_
        simp [UpperTheory.Gal.Schur.scaleAt, Finset.ne_of_mem_erase hk]
    have hC : UpperTheory.Gal.Schur.detOne ((algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₁ (α s)))
        (UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₁) =
        (1 - starRingEnd ℂ (t₀ (α s : F)) * starRingEnd ℂ (r t₀ i)) *
          ∏ k ∈ Finset.univ.erase i, (1 - starRingEnd ℂ (t₀ (α s : F)) * (y * starRingEnd ℂ (r t₀ k))) := by
      rw [detOne_eq_mul_prod_erase _ _ i, hx1]
      have htw : UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₁ =
          UpperTheory.Gal.Schur.scaleOff y i (fun j => starRingEnd ℂ (r t₀ j)) := by
        simp [UpperTheory.Gal.Schur.twist, hg1, h01.symm]
      rw [htw]
      congr 1
      · simp [UpperTheory.Gal.Schur.scaleOff]
      · refine Finset.prod_congr rfl fun k hk => ?_
        simp [UpperTheory.Gal.Schur.scaleOff, Finset.ne_of_mem_erase hk]
    have hE : ∀ τ ∈ (Finset.univ.erase t₀).erase t₁,
        (Multiset.map (fun z => 1 - τ (α s : F) * (y ^ ε τ * z)) (rts χ τ)).prod =
          UpperTheory.Gal.Schur.detOne ((algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO τ (α s)))
            (UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g τ) := by
      intro τ hτ
      have hτ1 := Finset.ne_of_mem_erase hτ
      have hτ0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hτ)
      rw [hr τ, Multiset.map_map]
      have htw : UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g τ = fun k => y ^ ε τ * r τ k := by
        simp [UpperTheory.Gal.Schur.twist, hτ0, hτ1, hgτ τ hτ1]
      rw [htw]
      rfl
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t₀),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ t₁⟩),
      hA, hC, ← Finset.prod_congr rfl hE]
    unfold fibW
    rw [hB, hB]
    ring
  · unfold ballW
    rw [hB, hg0]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Ring.inverse_eq_inv', div_eq_mul_inv]
