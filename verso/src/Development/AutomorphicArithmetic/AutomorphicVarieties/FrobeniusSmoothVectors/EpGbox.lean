import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpGflag

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h i j e => h i j e, fun h _ _ e => h e⟩`.
-/
private theorem upT_bt {K : Type} [CommRing K] {n : ℕ} {A : Matrix (Fin n) (Fin n) K} :
    UpT A ↔ A.BlockTriangular id := ⟨fun h i j e => h i j e, fun h _ _ e => h e⟩

/- English proof (translation)
The claim follows from `upT_bt.2 ((upT_bt.1 hA).mul (upT_bt.1 hB))`.
-/
private theorem upT_mul' {K : Type} [CommRing K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : UpT A) (hB : UpT B) :
    UpT (A * B) := upT_bt.2 ((upT_bt.1 hA).mul (upT_bt.1 hB))

/- English proof (translation)
Use `letI := u.invertible`. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `upT_bt.2 (Matrix.blockTriangular_inv_of_blockTriangular (upT_bt.1 h))`.
-/
private theorem upT_inv {K : Type} [CommRing K] {n : ℕ} {u : GL (Fin n) K} (h : UpT (u : Matrix (Fin n) (Fin n) K)) :
    UpT ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  letI := u.invertible
  rw [Matrix.coe_units_inv]
  exact upT_bt.2 (Matrix.blockTriangular_inv_of_blockTriangular (upT_bt.1 h))

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Introduce `b _ hb`. Break down `lt_or_gt_of_ne hb with e | e` into its components or cases. Rewrite using `[hA i b e, zero_mul]`. Rewrite using `[hB b i e, mul_zero]`.

Simplify using the standard rewrite rules.
-/
private theorem upT_diag {K : Type} [CommRing K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : UpT A) (hB : UpT B)
    (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with e | e
    · rw [hA i b e, zero_mul]
    · rw [hB b i e, mul_zero]
  · simp

/- English proof (translation)
Rewrite using `[_root_.mul_inv_rev, Units.val_mul, Units.val_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
private theorem conj_assoc {K : Type} [CommRing K] {n : ℕ} (u g : GL (Fin n) K) (M : Matrix (Fin n) (Fin n) K) :
    ((u * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * (((u * g)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (u : Matrix (Fin n) (Fin n) K) * ((g : Matrix (Fin n) (Fin n) K) * M *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `e` using `upT_diag h (upT_inv h) i`. Rewrite `e` using `[Units.mul_inv, Matrix.one_apply_eq]`. Rewrite using `[upT_diag (upT_mul' h hT) (upT_inv h), upT_diag h hT, mul_right_comm, ← e, one_mul]`.
-/
private theorem conj_diag {K : Type} [CommRing K] {n : ℕ} {u : GL (Fin n) K} (h : UpT (u : Matrix (Fin n) (Fin n) K))
    {T : Matrix (Fin n) (Fin n) K} (hT : UpT T) (i : Fin n) :
    ((u : Matrix (Fin n) (Fin n) K) * T * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i i = T i i := by
  have e := upT_diag h (upT_inv h) i
  rw [Units.mul_inv, Matrix.one_apply_eq] at e
  rw [upT_diag (upT_mul' h hT) (upT_inv h), upT_diag h hT, mul_right_comm, ← e, one_mul]

/- English proof (translation)
Introduce `l _ k _ F O _ _ _ _ h2 hc R _ _ _ σ hσ ρ B₀ hB hG hr hψ`. Establish `hr' : ∀ g, GrM σ pq pq (ρ.r g)` using `fun g a b => pw_eq a b ▸ hr g a b`. Establish `hres : ∀ v s, (B₀.r (F.loc v s)).mat = ρ.r (F.loc0 v s)` using `fun v s => hB.res (F.loc0 v s)`. Establish `htri : ∀ v s, UpT ((B₀.g v : Matrix (Fin 3) (Fin 3) R) * ρ.r (F.loc0 v s) * (((B₀.g v)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R))` using `fun v s => hres v s ▸ B₀.tri v s`. Establish `key : ∀ v, ∃ (u : GL (Fin 3) R) (α : Fin 3 → ZMod 2), UpT (u : Matrix (Fin 3) (Fin 3) R) ∧ GrM σ α pq ((u * B₀.g v : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)` using `fun v => by`.

Use `ep_gflag O h2 R σ hσ (fun s => ρ.r (F.loc0 v s)) (B₀.g v) (fun s => hr' _) (htri v) (fun s i => by rw [hB.psi]; exact hψ v i s) ?_` and prove the remaining obligations. Take `⟨s, hs⟩` from `hG.ψd v`. Use `⟨s, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[hB.psi, hB.psi]`. Assume the negation of the conclusion as `hu`.

Establish `hm : (ρ.ψ v i s : R) - ρ.ψ v j s ∈ maximalIdeal R` using `hu`. Rewrite `hm` using `[← res_eq_zero_iff (O := O), map_sub, sub_eq_zero]`. Conclude with `hs i j hij (Units.ext hm)`. Use `choose u π hu hg using key`. Use `⟨⟨B₀.r, B₀.nu, fun v => u v * B₀.g v, fun v s => ?_⟩, π, ⟨hB.atc, hB.res, fun v i s => ?_⟩, rfl, fun s => ?_, hg⟩` and prove the remaining obligations.

Rewrite using `[conj_assoc]`. Conclude with `upT_mul' (upT_mul' (hu v) (B₀.tri v s)) (upT_inv (hu v))`. Use `show (((u v * B₀.g v : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * ρ.r (F.loc0 v s) * (((u v * B₀.g v)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) i i = _`. Rewrite using `[conj_assoc, conj_diag (hu v) (htri v s), hB.psi]`. Use `show GrM σ pq pq (B₀.r s).mat`.

Break down `Int.units_eq_one_or (F.del s) with e | e` into its components or cases. Conclude with `hB.res ⟨s, e⟩ ▸ hr' ⟨s, e⟩`. Establish `hm : s * F.c⁻¹ ∈ F.del.ker`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, e, hc, mul_inv_cancel]`. Establish `h1 : (B₀.r F.c).left = 1` using `Units.ext hB.atc`.

Establish `h3 : (B₀.r s).mat = (B₀.r (s * F.c⁻¹)).mat` using `by conv_lhs => rw [← inv_mul_cancel_right s F.c, map_mul]`. Unfold `GG.mat`. Rewrite using `[SemidirectProduct.mul_left, h1, map_one, mul_one]`. Rewrite using `[h3]`. Conclude with `hB.res ⟨_, hm⟩ ▸ hr' ⟨_, hm⟩`.
-/
theorem UpperTheory.V.Fr.ep_gbox :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → F.del F.c = -1 → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ (ρ : NRep F 3 R) (B₀ : Box F 3 R), B₀.Of ρ → (ρ.bar O).Good → (∀ g a b, ρ.r g a b ∈ evp σ (pw a b)) → (∀ v i s, (ρ.ψ v i s : R) ∈ evp σ 0) → ∃ (B : Box F 3 R) (π : F.V → Fin 3 → ZMod 2), B.Of ρ ∧ B.r = B₀.r ∧ B.Gr σ π := by
  intro l _ k _ F O _ _ _ _ h2 hc R _ _ _ σ hσ ρ B₀ hB hG hr hψ
  have hr' : ∀ g, GrM σ pq pq (ρ.r g) := fun g a b => pw_eq a b ▸ hr g a b
  have hres : ∀ v s, (B₀.r (F.loc v s)).mat = ρ.r (F.loc0 v s) := fun v s => hB.res (F.loc0 v s)
  have htri : ∀ v s, UpT ((B₀.g v : Matrix (Fin 3) (Fin 3) R) * ρ.r (F.loc0 v s) *
      (((B₀.g v)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) := fun v s => hres v s ▸ B₀.tri v s
  have key : ∀ v, ∃ (u : GL (Fin 3) R) (α : Fin 3 → ZMod 2), UpT (u : Matrix (Fin 3) (Fin 3) R) ∧
      GrM σ α pq ((u * B₀.g v : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := fun v => by
    refine ep_gflag O h2 R σ hσ (fun s => ρ.r (F.loc0 v s)) (B₀.g v) (fun s => hr' _) (htri v)
      (fun s i => by rw [hB.psi]; exact hψ v i s) ?_
    obtain ⟨s, hs⟩ := hG.ψd v
    refine ⟨s, fun i j hij => ?_⟩
    rw [hB.psi, hB.psi]
    by_contra hu
    have hm : (ρ.ψ v i s : R) - ρ.ψ v j s ∈ maximalIdeal R := hu
    rw [← res_eq_zero_iff (O := O), map_sub, sub_eq_zero] at hm
    exact hs i j hij (Units.ext hm)
  choose u π hu hg using key
  refine ⟨⟨B₀.r, B₀.nu, fun v => u v * B₀.g v, fun v s => ?_⟩, π, ⟨hB.atc, hB.res, fun v i s => ?_⟩, rfl,
    fun s => ?_, hg⟩
  · rw [conj_assoc]
    exact upT_mul' (upT_mul' (hu v) (B₀.tri v s)) (upT_inv (hu v))
  · show (((u v * B₀.g v : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * ρ.r (F.loc0 v s) *
      (((u v * B₀.g v)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) i i = _
    rw [conj_assoc, conj_diag (hu v) (htri v s), hB.psi]
  · show GrM σ pq pq (B₀.r s).mat
    rcases Int.units_eq_one_or (F.del s) with e | e
    · exact hB.res ⟨s, e⟩ ▸ hr' ⟨s, e⟩
    · have hm : s * F.c⁻¹ ∈ F.del.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, e, hc, mul_inv_cancel]
      have h1 : (B₀.r F.c).left = 1 := Units.ext hB.atc
      have h3 : (B₀.r s).mat = (B₀.r (s * F.c⁻¹)).mat := by
        conv_lhs => rw [← inv_mul_cancel_right s F.c, map_mul]
        unfold GG.mat
        rw [SemidirectProduct.mul_left, h1, map_one, mul_one]
      rw [h3]
      exact hB.res ⟨_, hm⟩ ▸ hr' ⟨_, hm⟩
