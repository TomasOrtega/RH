import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.RelMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DTwAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Infres
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Shapiro
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CornerCoc

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `g _ h _`. Use `show ∑ k, α k • z k (g * h) = ∑ k, α k • z k g + χ g • (r g * (∑ k, α k • z k h) * r g⁻¹)`. Rewrite using `[Finset.sum_congr rfl fun k _ => by rw [hz k g (Set.mem_univ _) h (Set.mem_univ _)]]`. Simplify using `[smul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]`.
-/
private theorem coc_comb {F G : Type} [Field F] [Group G] {n m : ℕ} (χ : G → F)
    (r : G → Matrix (Fin n) (Fin n) F) (z : Fin m → G → Matrix (Fin n) (Fin n) F) (α : Fin m → F)
    (hz : ∀ k, TwCoc χ r Set.univ (z k)) : TwCoc χ r Set.univ fun g => ∑ k, α k • z k g := by
  intro g _ h _
  show ∑ k, α k • z k (g * h) = ∑ k, α k • z k g + χ g • (r g * (∑ k, α k • z k h) * r g⁻¹)
  rw [Finset.sum_congr rfl fun k _ => by rw [hz k g (Set.mem_univ _) h (Set.mem_univ _)]]
  simp [smul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Use `split_ifs with h`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : q k ↔ q j`. Rewrite using `[if_pos ⟨h.1, hk.2 h.2⟩]`.

Rewrite using `[hB k j hk, mul_zero, mul_zero]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : q k ↔ q j`. Rewrite using `[if_neg (fun h' => h ⟨h'.1, hk.1 h'.2⟩), zero_mul]`. Rewrite using `[hB k j hk, mul_zero]`.
-/
private theorem cut_mul {F : Type} [Field F] {n : ℕ} (p q : Fin n → Prop) [∀ i j, Decidable (p i ∧ q j)]
    (Z B : Matrix (Fin n) (Fin n) F) (hB : ∀ k j, ¬ (q k ↔ q j) → B k j = 0) (i j : Fin n) :
    ((Matrix.of fun i j => if p i ∧ q j then Z i j else 0) * B) i j = if p i ∧ q j then (Z * B) i j else 0 := by
  simp only [Matrix.mul_apply, Matrix.of_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : q k ↔ q j
    · rw [if_pos ⟨h.1, hk.2 h.2⟩]
    · rw [hB k j hk, mul_zero, mul_zero]
  · refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : q k ↔ q j
    · rw [if_neg (fun h' => h ⟨h'.1, hk.1 h'.2⟩), zero_mul]
    · rw [hB k j hk, mul_zero]

/- English proof (translation)
Introduce `c hc hs`. Establish `hev : ∀ g k l, ¬ (q k ↔ q l) → D.r g k l = 0`. Introduce `g k l h`. Conclude with `(Submodule.mem_bot F).1 (((D.ev g) k l).2 (hq k l h))`. Establish `e : ∀ g, ((Matrix.of fun i j => if p i ∧ q j then z g i j else 0) * D.r g) i j = if p i ∧ q j then (z g * D.r g) i j else 0` using `fun g => cut_mul p q (z g) (D.r g) (hev g) i j`.

Simplify using `only [Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, e]`. Use `split_ifs with h`. Use `hk i j h.1 h.2 c hc hs` as an intermediate fact. Simplify `this` using `[Finsupp.sum, Matrix.sum_apply]`. Simplify using the standard rewrite rules.
-/
private theorem kills_cut {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (p q : Fin n → Prop) [∀ i j, Decidable (p i ∧ q j)] (z : G → Matrix (Fin n) (Fin n) F)
    (hq : ∀ k j, ¬ (q k ↔ q j) → ¬ ((k : ℕ) < D.a ↔ (j : ℕ) < D.a))
    (hk : ∀ i j, p i → q j → D.KillsRel z i j) (i j : Fin n) :
    D.KillsRel (fun g => Matrix.of fun i j => if p i ∧ q j then z g i j else 0) i j := by
  intro c hc hs
  have hev : ∀ g k l, ¬ (q k ↔ q l) → D.r g k l = 0 := by
    intro g k l h
    exact (Submodule.mem_bot F).1 (((D.ev g) k l).2 (hq k l h))
  have e : ∀ g, ((Matrix.of fun i j => if p i ∧ q j then z g i j else 0) * D.r g) i j
      = if p i ∧ q j then (z g * D.r g) i j else 0 := fun g => cut_mul p q (z g) (D.r g) (hev g) i j
  simp only [Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, e]
  split_ifs with h
  · have := hk i j h.1 h.2 c hc hs
    simpa [Finsupp.sum, Matrix.sum_apply] using this
  · simp

/- English proof (translation)
Establish `hKL : TwCoc (fun _ => (1 : F)) D.r D.G' (fun g => K g + L g)`. Introduce `g hg h _`. Establish `e1 : K (g * h) = K g + D.r g * K h * D.r g⁻¹` using `by simpa using hK g trivial h trivial`. Establish `e2 : L (g * h) = L g + D.r g * L h * D.r g⁻¹`. Simplify `hL g trivial h trivial` using `[DetFr.χF, D.χ_triv g hg]`.

Use `show K (g * h) + L (g * h) = K g + L g + (1 : F) • (D.r g * (K h + L h) * D.r g⁻¹)`. Rewrite using `[e1, e2, one_smul, Matrix.mul_add, Matrix.add_mul]`. Normalize the expressions using the abelian group laws. Take `⟨Y, hY⟩` from `Det.der D _ hKL hk`. Take `⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩` from `Det.eigen D K L Y hK hL hY`.

Establish `hχ1 : ∀ g ∈ D.G', D.χF g = 1` using `by intro g hg; simp [DetFr.χF, D.χ_triv g hg]`. Establish `hY2' : ∀ g ∈ D.G', L g = dTw D.χF D.r Y2 g`. Introduce `g hg`. Rewrite using `[hY2 g hg]`. Simplify using `[dTw, hχ1 g hg]`.

Take `⟨Z1, -, hZ1⟩` from `Det.infres D (fun _ => 1) K Y1 (by intros; simp) (by intros; rfl) hK hKo hY1`. Take `⟨Z2, -, hZ2⟩` from `Det.infres D D.χF L Y2 (by intro g h; simp [DetFr.χF]) hχ1 hL hLo hY2'`. Conclude with `⟨⟨Z1, hZ1⟩, ⟨Z2, hZ2⟩⟩`.
-/
private theorem block_princ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n)
    (K L : G → Matrix (Fin n) (Fin n) F) (hK : TwCoc (fun _ => 1) D.r Set.univ K)
    (hL : TwCoc D.χF D.r Set.univ L) (hKo : ∀ g, K g ∈ Od F F n D.a) (hLo : ∀ g, L g ∈ Od F F n D.a)
    (hk : ∀ i j, D.KillsRel (fun g => K g + L g) i j) :
    (∃ Y, ∀ g, K g = dTw (fun _ => 1) D.r Y g) ∧ ∃ Y, ∀ g, L g = dTw D.χF D.r Y g := by
  have hKL : TwCoc (fun _ => (1 : F)) D.r D.G' (fun g => K g + L g) := by
    intro g hg h _
    have e1 : K (g * h) = K g + D.r g * K h * D.r g⁻¹ := by simpa using hK g trivial h trivial
    have e2 : L (g * h) = L g + D.r g * L h * D.r g⁻¹ := by
      simpa [DetFr.χF, D.χ_triv g hg] using hL g trivial h trivial
    show K (g * h) + L (g * h) = K g + L g + (1 : F) • (D.r g * (K h + L h) * D.r g⁻¹)
    rw [e1, e2, one_smul, Matrix.mul_add, Matrix.add_mul]
    abel
  obtain ⟨Y, hY⟩ := Det.der D _ hKL hk
  obtain ⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩ := Det.eigen D K L Y hK hL hY
  have hχ1 : ∀ g ∈ D.G', D.χF g = 1 := by intro g hg; simp [DetFr.χF, D.χ_triv g hg]
  have hY2' : ∀ g ∈ D.G', L g = dTw D.χF D.r Y2 g := by
    intro g hg
    rw [hY2 g hg]
    simp [dTw, hχ1 g hg]
  obtain ⟨Z1, -, hZ1⟩ := Det.infres D (fun _ => 1) K Y1 (by intros; simp) (by intros; rfl) hK hKo hY1
  obtain ⟨Z2, -, hZ2⟩ := Det.infres D D.χF L Y2 (by intro g h; simp [DetFr.χF]) hχ1 hL hLo hY2'
  exact ⟨⟨Z1, hZ1⟩, ⟨Z2, hZ2⟩⟩

/- English proof (translation)
Introduce `F G _ _ n D m κ la s ph hκ hla α β i j hij hkill`. Take `⟨K, hKe⟩ : ∃ K : G → Matrix (Fin n) (Fin n) F, K = fun g => ∑ k, α k • κ k g` from `⟨_, rfl⟩`. Take `⟨L, hLe⟩ : ∃ L : G → Matrix (Fin n) (Fin n) F, L = fun g => ∑ k, β k • la k g` from `⟨_, rfl⟩`. Rewrite `hkill` using `[show (fun g => ∑ k, α k • κ k g + ∑ k, β k • la k g) = fun g => K g + L g by rw [hKe, hLe]]`. Establish `hKc : TwCoc (fun _ => (1 : F)) D.r Set.univ K` using `by rw [hKe]; exact coc_comb _ _ κ α hκ.coc`.

Establish `hLc : TwCoc D.χF D.r Set.univ L` using `by rw [hLe]; exact coc_comb _ _ la β hla.coc`. Establish `hKo : ∀ g, K g ∈ Od F F n D.a` using `fun g => by`. Rewrite using `[hKe]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hκ.od k g)`. Establish `hLo : ∀ g, L g ∈ Od F F n D.a` using `fun g => by`.

Rewrite using `[hLe]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hla.od k g)`. Establish `hKp : ∀ g, K (D.σ g) = (-1 : F) • (K g)ᵀ`. Introduce `g`. Rewrite using `[hKe]`.

Simplify using `[hκ.pol, Matrix.transpose_sum]`. Establish `hLp : ∀ g, L (D.σ g) = s • (L g)ᵀ`. Introduce `g`. Rewrite using `[hLe]`. Simplify using `[hla.pol, Matrix.transpose_sum, Finset.smul_sum, smul_smul, mul_comm]`.

Establish `hTot : TwCoc (fun _ => (1 : F)) D.r D.G' (fun g => K g + L g)`. Introduce `g hg h _`. Establish `e1 : K (g * h) = K g + D.r g * K h * D.r g⁻¹` using `by simpa using hKc g trivial h trivial`. Establish `e2 : L (g * h) = L g + D.r g * L h * D.r g⁻¹`. Simplify `hLc g trivial h trivial` using `[DetFr.χF, D.χ_triv g hg]`.

Use `show K (g * h) + L (g * h) = K g + L g + (1 : F) • (D.r g * (K h + L h) * D.r g⁻¹)`. Rewrite using `[e1, e2, one_smul, Matrix.mul_add, Matrix.add_mul]`. Normalize the expressions using the abelian group laws. Take `⟨p, hpd⟩ : ∃ p : Fin n → Prop, ∀ x, p x ↔ ((x : ℕ) < D.a ↔ (i : ℕ) < D.a)` from `⟨_, fun _ => Iff.rfl⟩`. Take `⟨q, hqd⟩ : ∃ q : Fin n → Prop, ∀ x, q x ↔ ((x : ℕ) < D.a ↔ (j : ℕ) < D.a)` from `⟨_, fun _ => Iff.rfl⟩`.

Establish `hq : ∀ k l, ¬ (q k ↔ q l) → ¬ ((k : ℕ) < D.a ↔ (l : ℕ) < D.a)`. Introduce `k l h h'`. Apply `h` to reduce the goal to its premises. Rewrite using `[hqd k, hqd l]`. The claim follows by propositional logic.

Establish `hk' : ∀ i' j', p i' → q j' → D.KillsRel (fun g => K g + L g) i' j'` using `fun i' j' hi' hj' => Det.relMove D _ i j hTot hkill i' j' ((hpd i').1 hi').symm ((hqd j').1 hj').symm`. Establish `cK` using `Det.cornerCoc D _ _ _ hKc`. Establish `cL` using `Det.cornerCoc D _ _ _ hLc`. Establish `hcase : ((i : ℕ) < D.a ∧ ¬ (j : ℕ) < D.a) ∨ (¬ (i : ℕ) < D.a ∧ (j : ℕ) < D.a)` using `by tauto`. Establish `key : ∃ Y1 Y2, ((∀ g, cV D.a (K g) = dTw (fun _ => (1 : F)) D.r Y1 g) ∨ (∀ g, cV' D.a (K g) = dTw (fun _ => (1 : F)) D.r Y1 g)) ∧ ((∀ g, cV D.a (L g) = dTw D.χF D.r Y2 g) ∨ (∀ g, cV' D.a (L g) = dTw D.χF D.r Y2 g))`.

Break down `hcase with ⟨hi, hj⟩ | ⟨hi, hj⟩` into its components or cases. Establish `hc2 : ∀ i' j', D.KillsRel (fun g => cV D.a (K g) + cV D.a (L g)) i' j'`. Introduce `i' j'`. Rewrite using `[show (fun g => cV D.a (K g) + cV D.a (L g)) = fun g => Matrix.of fun a b => if p a ∧ q b then (K g + L g) a b else 0 by`. Use function extensionality and compare the values at `g`.

Use extensionality with `a b`. Establish `hpa : p a ↔ (a : ℕ) < D.a` using `by rw [hpd]; tauto`. Establish `hqb : q b ↔ ¬ (b : ℕ) < D.a` using `by rw [hqd]; tauto`. Simplify using `only [cV, Matrix.of_apply, Matrix.add_apply]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; tauto) | simp]`.

Conclude with `kills_cut D p q (fun g => K g + L g) hq hk' i' j'`. Take `⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩` from `block_princ D (fun g => cV D.a (K g)) (fun g => cV D.a (L g)) cK.1 cL.1 (fun g => (cK.2.2.2 (K g)).1) (fun g => (cL.2.2.2 (L g)).1) hc2`. Conclude with `⟨Y1, Y2, Or.inl hY1, Or.inl hY2⟩`. Establish `hc2 : ∀ i' j', D.KillsRel (fun g => cV' D.a (K g) + cV' D.a (L g)) i' j'`. Introduce `i' j'`.

Rewrite using `[show (fun g => cV' D.a (K g) + cV' D.a (L g)) = fun g => Matrix.of fun a b => if p a ∧ q b then (K g + L g) a b else 0 by`. Use function extensionality and compare the values at `g`. Use extensionality with `a b`. Establish `hpa : p a ↔ ¬ (a : ℕ) < D.a` using `by rw [hpd]; tauto`. Establish `hqb : q b ↔ (b : ℕ) < D.a` using `by rw [hqd]; tauto`.

Simplify using `only [cV', Matrix.of_apply, Matrix.add_apply]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; tauto) | simp]`. Conclude with `kills_cut D p q (fun g => K g + L g) hq hk' i' j'`. Take `⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩` from `block_princ D (fun g => cV' D.a (K g)) (fun g => cV' D.a (L g)) cK.2.1 cL.2.1 (fun g => (cK.2.2.2 (K g)).2.1) (fun g => (cL.2.2.2 (L g)).2.1) hc2`. Conclude with `⟨Y1, Y2, Or.inr hY1, Or.inr hY2⟩`.

Take `⟨Y1, Y2, hK1, hL2⟩` from `key`. Take `⟨YK, hYKo, hYKs, hYK⟩` from `Det.shapiro D (fun _ => (1 : F)) (-1) K Y1 (fun _ => rfl) (by norm_num) hKc hKo hKp hK1`. Take `⟨YL, hYLo, hYLs, hYL⟩` from `Det.shapiro D D.χF s L Y2 (fun g => by simp [DetFr.χF, D.χσ]) hla.sq hLc hLo hLp hL2`. Establish `hT : YKᵀ = -YK`. Establish `h` using `congrArg Matrix.transpose hYKs`.

Simplify using `only [Matrix.transpose_smul, Matrix.transpose_transpose, neg_smul, one_smul] at h`. Conclude with `h.symm`. Establish `hα : α = 0` using `hκ.indep α YK hYKo hT fun g => by`. Use `hYK g` as an intermediate fact. Rewrite `this` using `[hKe]`.

Conclude with `this`. Conclude with `⟨hα, YL, hYLo, hYLs, fun g => by`. Use `hYL g` as an intermediate fact. Rewrite `this` using `[hLe]`. Conclude with `this⟩`.
-/
theorem UpperTheory.V.Pa.Det.ann :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) {m : ℕ} (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F), D.IsKap κ → D.IsTw κ s ph la → ∀ (α β : Fin m → F) (i j : Fin n), ¬ (((i : ℕ) < D.a) ↔ ((j : ℕ) < D.a)) → D.KillsRel (fun g => ∑ k, α k • κ k g + ∑ k, β k • la k g) i j → α = 0 ∧ ∃ Y ∈ Od F F n D.a, s • Yᵀ = Y ∧ ∀ g, ∑ k, β k • la k g = dTw D.χF D.r Y g := by
  classical
  intro F G _ _ n D m κ la s ph hκ hla α β i j hij hkill
  obtain ⟨K, hKe⟩ : ∃ K : G → Matrix (Fin n) (Fin n) F, K = fun g => ∑ k, α k • κ k g := ⟨_, rfl⟩
  obtain ⟨L, hLe⟩ : ∃ L : G → Matrix (Fin n) (Fin n) F, L = fun g => ∑ k, β k • la k g := ⟨_, rfl⟩
  rw [show (fun g => ∑ k, α k • κ k g + ∑ k, β k • la k g) = fun g => K g + L g by rw [hKe, hLe]] at hkill
  have hKc : TwCoc (fun _ => (1 : F)) D.r Set.univ K := by rw [hKe]; exact coc_comb _ _ κ α hκ.coc
  have hLc : TwCoc D.χF D.r Set.univ L := by rw [hLe]; exact coc_comb _ _ la β hla.coc
  have hKo : ∀ g, K g ∈ Od F F n D.a := fun g => by
    rw [hKe]; exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hκ.od k g)
  have hLo : ∀ g, L g ∈ Od F F n D.a := fun g => by
    rw [hLe]; exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hla.od k g)
  have hKp : ∀ g, K (D.σ g) = (-1 : F) • (K g)ᵀ := by
    intro g; rw [hKe]; simp [hκ.pol, Matrix.transpose_sum]
  have hLp : ∀ g, L (D.σ g) = s • (L g)ᵀ := by
    intro g; rw [hLe]; simp [hla.pol, Matrix.transpose_sum, Finset.smul_sum, smul_smul, mul_comm]
  have hTot : TwCoc (fun _ => (1 : F)) D.r D.G' (fun g => K g + L g) := by
    intro g hg h _
    have e1 : K (g * h) = K g + D.r g * K h * D.r g⁻¹ := by simpa using hKc g trivial h trivial
    have e2 : L (g * h) = L g + D.r g * L h * D.r g⁻¹ := by
      simpa [DetFr.χF, D.χ_triv g hg] using hLc g trivial h trivial
    show K (g * h) + L (g * h) = K g + L g + (1 : F) • (D.r g * (K h + L h) * D.r g⁻¹)
    rw [e1, e2, one_smul, Matrix.mul_add, Matrix.add_mul]
    abel
  obtain ⟨p, hpd⟩ : ∃ p : Fin n → Prop, ∀ x, p x ↔ ((x : ℕ) < D.a ↔ (i : ℕ) < D.a) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q : Fin n → Prop, ∀ x, q x ↔ ((x : ℕ) < D.a ↔ (j : ℕ) < D.a) := ⟨_, fun _ => Iff.rfl⟩
  have hq : ∀ k l, ¬ (q k ↔ q l) → ¬ ((k : ℕ) < D.a ↔ (l : ℕ) < D.a) := by
    intro k l h h'
    apply h
    rw [hqd k, hqd l]
    tauto
  have hk' : ∀ i' j', p i' → q j' → D.KillsRel (fun g => K g + L g) i' j' := fun i' j' hi' hj' =>
    Det.relMove D _ i j hTot hkill i' j' ((hpd i').1 hi').symm ((hqd j').1 hj').symm
  have cK := Det.cornerCoc D _ _ _ hKc
  have cL := Det.cornerCoc D _ _ _ hLc
  have hcase : ((i : ℕ) < D.a ∧ ¬ (j : ℕ) < D.a) ∨ (¬ (i : ℕ) < D.a ∧ (j : ℕ) < D.a) := by tauto
  have key : ∃ Y1 Y2, ((∀ g, cV D.a (K g) = dTw (fun _ => (1 : F)) D.r Y1 g) ∨
      (∀ g, cV' D.a (K g) = dTw (fun _ => (1 : F)) D.r Y1 g)) ∧
      ((∀ g, cV D.a (L g) = dTw D.χF D.r Y2 g) ∨ (∀ g, cV' D.a (L g) = dTw D.χF D.r Y2 g)) := by
    rcases hcase with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hc2 : ∀ i' j', D.KillsRel (fun g => cV D.a (K g) + cV D.a (L g)) i' j' := by
        intro i' j'
        rw [show (fun g => cV D.a (K g) + cV D.a (L g)) =
            fun g => Matrix.of fun a b => if p a ∧ q b then (K g + L g) a b else 0 by
          funext g
          ext a b
          have hpa : p a ↔ (a : ℕ) < D.a := by rw [hpd]; tauto
          have hqb : q b ↔ ¬ (b : ℕ) < D.a := by rw [hqd]; tauto
          simp only [cV, Matrix.of_apply, Matrix.add_apply]
          split_ifs <;> first | rfl | (exfalso; tauto) | simp]
        exact kills_cut D p q (fun g => K g + L g) hq hk' i' j'
      obtain ⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩ := block_princ D (fun g => cV D.a (K g)) (fun g => cV D.a (L g))
        cK.1 cL.1 (fun g => (cK.2.2.2 (K g)).1) (fun g => (cL.2.2.2 (L g)).1) hc2
      exact ⟨Y1, Y2, Or.inl hY1, Or.inl hY2⟩
    · have hc2 : ∀ i' j', D.KillsRel (fun g => cV' D.a (K g) + cV' D.a (L g)) i' j' := by
        intro i' j'
        rw [show (fun g => cV' D.a (K g) + cV' D.a (L g)) =
            fun g => Matrix.of fun a b => if p a ∧ q b then (K g + L g) a b else 0 by
          funext g
          ext a b
          have hpa : p a ↔ ¬ (a : ℕ) < D.a := by rw [hpd]; tauto
          have hqb : q b ↔ (b : ℕ) < D.a := by rw [hqd]; tauto
          simp only [cV', Matrix.of_apply, Matrix.add_apply]
          split_ifs <;> first | rfl | (exfalso; tauto) | simp]
        exact kills_cut D p q (fun g => K g + L g) hq hk' i' j'
      obtain ⟨⟨Y1, hY1⟩, ⟨Y2, hY2⟩⟩ := block_princ D (fun g => cV' D.a (K g)) (fun g => cV' D.a (L g))
        cK.2.1 cL.2.1 (fun g => (cK.2.2.2 (K g)).2.1) (fun g => (cL.2.2.2 (L g)).2.1) hc2
      exact ⟨Y1, Y2, Or.inr hY1, Or.inr hY2⟩
  obtain ⟨Y1, Y2, hK1, hL2⟩ := key
  obtain ⟨YK, hYKo, hYKs, hYK⟩ :=
    Det.shapiro D (fun _ => (1 : F)) (-1) K Y1 (fun _ => rfl) (by norm_num) hKc hKo hKp hK1
  obtain ⟨YL, hYLo, hYLs, hYL⟩ :=
    Det.shapiro D D.χF s L Y2 (fun g => by simp [DetFr.χF, D.χσ]) hla.sq hLc hLo hLp hL2
  have hT : YKᵀ = -YK := by
    have h := congrArg Matrix.transpose hYKs
    simp only [Matrix.transpose_smul, Matrix.transpose_transpose, neg_smul, one_smul] at h
    exact h.symm
  have hα : α = 0 := hκ.indep α YK hYKo hT fun g => by
    have := hYK g
    rw [hKe] at this
    exact this
  exact ⟨hα, YL, hYLo, hYLs, fun g => by
    have := hYL g
    rw [hLe] at this
    exact this⟩
