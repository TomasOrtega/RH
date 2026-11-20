import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ L G G0 h n x k c hc`. Take `⟨Y, hY, hYt, hcY⟩` from `hc`. Establish `hinj : Function.Injective (algebraMap x.A x.Fr)` using `IsFractionRing.injective x.A x.Fr`. Establish `hsurj : Function.Surjective h.p₀`. Introduce and unpack `⟨g', hg'⟩`.

Take `⟨γ, hγ⟩` from `h.surj g'`. Use `⟨⟨γ, ?_⟩, Subtype.ext hγ⟩` and prove the remaining obligations. Use `show G.η γ = 1`. Rewrite using `[← h.η, hγ]`. Conclude with `hg'`.

Establish `hb : ∃ b : nonZeroDivisors x.A, ∀ i : Fin k.g ⊕ (Fin n × Fin n), ∃ r : x.A, algebraMap x.A x.Fr r = (b : x.A) • Sum.elim c (fun p => Y p.1 p.2) i` using `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors x.A) _`. Take `⟨b, hb⟩` from `hb`. Use `choose a ha using hb`. Set `cA : Fin k.g → x.A` to `fun j => a (Sum.inl j)`. Set `YA : Matrix (Fin n) (Fin n) x.A` to `fun i j => a (Sum.inr (i, j))`.

Set `ψ` to `(Algebra.ofId x.A x.Fr).mapMatrix (m := Fin n)`. Establish `hψ : ∀ M : Matrix (Fin n) (Fin n) x.A, ψ M = M.map (algebraMap x.A x.Fr)` using `fun M => rfl`. Establish `hψinj : Function.Injective ψ`. Introduce `M N hMN`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Apply `hinj` to reduce the goal to its premises. Use `congrFun (congrFun hMN i) j` as an intermediate fact. Rewrite `this` using `[hψ, hψ]`. Then use the resulting hypothesis. Establish `hψY : ψ YA = (b : x.A) • Y`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Rewrite using `[hψ]`. Conclude with `ha (Sum.inr (i, j))`. Establish `hρ : ∀ g, ψ (x.ρX x.A g) = x.ρX x.Fr g`. Introduce `g`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Simplify using `[hψ, NP.ρX]`. Establish `hκ : ∀ j γ, ψ (k.κ j (h.p₀ γ)) = kapF h k j γ` using `fun j γ => rfl`. Establish `hcj : ∀ j (M : Matrix (Fin n) (Fin n) x.Fr), cA j • M = (b : x.A) • (c j • M)`. Introduce `j M`. Rewrite using `[← algebraMap_smul x.Fr (cA j) M, ha (Sum.inl j), Sum.elim_inl, smul_assoc]`.

Establish `hmem : ∑ j, cA j • k.κ j ∈ Bd G0.frame (x.ρX x.A) (Od x.A x.A n x.a)`. Use `⟨YA, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Use `⟨fun hij => ?_, fun _ => Submodule.mem_top⟩` and prove the remaining obligations. Establish `h0 : Y i j = 0` using `(Submodule.mem_bot _).1 ((hY i j).1 hij)`.

Rewrite using `[Submodule.mem_bot]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use `ha (Sum.inr (i, j))` as an intermediate fact. Rewrite `this` using `[Sum.elim_inr, h0, smul_zero]`.

Conclude with `this`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises. Establish `h1` using `ha (Sum.inr (j, i))`. Establish `h2` using `ha (Sum.inr (i, j))`.

Rewrite `h1`, `h2` using `[Sum.elim_inr]`. Establish `hYij : Y j i = - Y i j` using `congrFun (congrFun hYt i) j`. Rewrite using `[Matrix.transpose_apply, Matrix.neg_apply, map_neg]`. Use `show algebraMap x.A x.Fr (a (Sum.inr (j, i))) = -algebraMap x.A x.Fr (a (Sum.inr (i, j)))`. Rewrite using `[h1, h2, hYij, smul_neg]`.

Use function extensionality and compare the values at `g'`. Take `⟨γ, rfl⟩` from `hsurj g'`. Apply `hψinj` to reduce the goal to its premises. Establish `hL : ψ ((∑ j, cA j • k.κ j) (h.p₀ γ)) = (b : x.A) • (∑ j, c j • kapF h k j) γ`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, hκ, hcj, Finset.smul_sum]`.

Rewrite using `[hL, hcY]`. Simplify using `only [dY, map_sub, map_mul, hρ, hψY, Matrix.mul_smul, Matrix.smul_mul, smul_sub, map_inv]`. Establish `hzero` using `k.indep cA hmem`. Use function extensionality and compare the values at `j`. Establish `hj` using `ha (Sum.inl j)`.

Establish `h0 : cA j = 0` using `congrFun hzero j`. Rewrite `hj` using `[Sum.elim_inl, Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `algebraMap x.A x.Fr (cA j) = _ at hj`. Rewrite `hj` using `[h0, map_zero]`. Establish `hb0 : algebraMap x.A x.Fr (b : x.A) ≠ 0` using `fun h0' => nonZeroDivisors.ne_zero b.2 (hinj (h0'.trans (map_zero _).symm))`.

Conclude with `(mul_eq_zero.1 hj.symm).resolve_left hb0`.
-/
theorem UpperTheory.V.Pa.indF :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ c : Fin k.g → x.Fr, ∑ j, c j • kapF h k j ∈ BdM h x x.Fr → c = 0 := by
  intro l _ L G G0 h n x k c hc
  classical
  obtain ⟨Y, hY, hYt, hcY⟩ := hc
  have hinj : Function.Injective (algebraMap x.A x.Fr) := IsFractionRing.injective x.A x.Fr
  have hsurj : Function.Surjective h.p₀ := by
    rintro ⟨g', hg'⟩
    obtain ⟨γ, hγ⟩ := h.surj g'
    refine ⟨⟨γ, ?_⟩, Subtype.ext hγ⟩
    show G.η γ = 1
    rw [← h.η, hγ]
    exact hg'
  have hb : ∃ b : nonZeroDivisors x.A, ∀ i : Fin k.g ⊕ (Fin n × Fin n),
      ∃ r : x.A, algebraMap x.A x.Fr r = (b : x.A) • Sum.elim c (fun p => Y p.1 p.2) i :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors x.A) _
  obtain ⟨b, hb⟩ := hb
  choose a ha using hb
  let cA : Fin k.g → x.A := fun j => a (Sum.inl j)
  let YA : Matrix (Fin n) (Fin n) x.A := fun i j => a (Sum.inr (i, j))
  let ψ := (Algebra.ofId x.A x.Fr).mapMatrix (m := Fin n)
  have hψ : ∀ M : Matrix (Fin n) (Fin n) x.A, ψ M = M.map (algebraMap x.A x.Fr) := fun M => rfl
  have hψinj : Function.Injective ψ := by
    intro M N hMN
    refine Matrix.ext fun i j => ?_
    apply hinj
    have := congrFun (congrFun hMN i) j
    rwa [hψ, hψ] at this
  have hψY : ψ YA = (b : x.A) • Y := by
    refine Matrix.ext fun i j => ?_
    rw [hψ]
    exact ha (Sum.inr (i, j))
  have hρ : ∀ g, ψ (x.ρX x.A g) = x.ρX x.Fr g := by
    intro g
    refine Matrix.ext fun i j => ?_
    simp [hψ, NP.ρX]
  have hκ : ∀ j γ, ψ (k.κ j (h.p₀ γ)) = kapF h k j γ := fun j γ => rfl
  have hcj : ∀ j (M : Matrix (Fin n) (Fin n) x.Fr), cA j • M = (b : x.A) • (c j • M) := by
    intro j M
    rw [← algebraMap_smul x.Fr (cA j) M, ha (Sum.inl j), Sum.elim_inl, smul_assoc]
  have hmem : ∑ j, cA j • k.κ j ∈ Bd G0.frame (x.ρX x.A) (Od x.A x.A n x.a) := by
    refine ⟨YA, ?_, ?_, ?_⟩
    · intro i j
      refine ⟨fun hij => ?_, fun _ => Submodule.mem_top⟩
      have h0 : Y i j = 0 := (Submodule.mem_bot _).1 ((hY i j).1 hij)
      rw [Submodule.mem_bot]
      apply hinj
      rw [map_zero]
      have := ha (Sum.inr (i, j))
      rw [Sum.elim_inr, h0, smul_zero] at this
      exact this
    · refine Matrix.ext fun i j => ?_
      apply hinj
      have h1 := ha (Sum.inr (j, i))
      have h2 := ha (Sum.inr (i, j))
      rw [Sum.elim_inr] at h1 h2
      have hYij : Y j i = - Y i j := congrFun (congrFun hYt i) j
      rw [Matrix.transpose_apply, Matrix.neg_apply, map_neg]
      show algebraMap x.A x.Fr (a (Sum.inr (j, i))) = -algebraMap x.A x.Fr (a (Sum.inr (i, j)))
      rw [h1, h2, hYij, smul_neg]
    · funext g'
      obtain ⟨γ, rfl⟩ := hsurj g'
      apply hψinj
      have hL : ψ ((∑ j, cA j • k.κ j) (h.p₀ γ)) = (b : x.A) • (∑ j, c j • kapF h k j) γ := by
        simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, hκ, hcj, Finset.smul_sum]
      rw [hL, hcY]
      simp only [dY, map_sub, map_mul, hρ, hψY, Matrix.mul_smul, Matrix.smul_mul, smul_sub, map_inv]
  have hzero := k.indep cA hmem
  funext j
  have hj := ha (Sum.inl j)
  have h0 : cA j = 0 := congrFun hzero j
  rw [Sum.elim_inl, Algebra.smul_def] at hj
  change algebraMap x.A x.Fr (cA j) = _ at hj
  rw [h0, map_zero] at hj
  have hb0 : algebraMap x.A x.Fr (b : x.A) ≠ 0 := fun h0' =>
    nonZeroDivisors.ne_zero b.2 (hinj (h0'.trans (map_zero _).symm))
  exact (mul_eq_zero.1 hj.symm).resolve_left hb0
