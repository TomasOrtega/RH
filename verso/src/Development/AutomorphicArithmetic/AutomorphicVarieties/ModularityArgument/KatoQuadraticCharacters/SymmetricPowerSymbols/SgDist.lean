import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAdmissibleSmoothingFactorDividedIndices

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

/- English proof (translation)
Use `haveI : NeZero M := ⟨hM.ne'⟩`. Use `⟨hc, h6, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨n0, hn0⟩, ⟨n1, hn1⟩⟩`. Apply `hx` to reduce the goal to its premises. Establish `hMq : (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`.

Establish `key : ∀ i : Fin 2, ∀ n : ℤ, (n : ℚ) = c * toQ M x i → x i = 0`. Introduce `i n hn`. Establish `hlt` using `ZMod.val_lt (x i)`. Establish `e : (n : ℚ) * M = (c * (x i).val : ℕ)`. Rewrite using `[hn, toQ]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `e' : n * (M : ℤ) = ((c * (x i).val : ℕ) : ℤ)` using `by exact_mod_cast e`. Establish `hd : (M : ℤ) ∣ ((c * (x i).val : ℕ) : ℤ)` using `⟨n, by rw [← e', mul_comm]⟩`. Establish `hd' : M ∣ c * (x i).val` using `by exact_mod_cast hd`.

Establish `hv : M ∣ (x i).val` using `(Nat.Coprime.symm hcM).dvd_of_dvd_mul_left hd'`. Establish `hv0 : (x i).val = 0`. Break down `Nat.eq_zero_or_pos (x i).val with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (Nat.le_of_dvd h hv) (not_le.mpr hlt)`.

Conclude with `(ZMod.val_eq_zero _).mp hv0`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `key 0 n0 hn0`. Conclude with `key 1 n1 hn1`.
-/
private theorem siegel_admissible_to_rat (c M : ℕ) (hc : 1 < c) (h6 : Nat.Coprime c 6) (hM : 0 < M) (hcM : Nat.Coprime c M)
    (x : Row M) (hx : x ≠ 0) : GlobalTheory.Sieg.admitted c (toQ M x) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  refine ⟨hc, h6, ?_⟩
  rintro ⟨⟨n0, hn0⟩, ⟨n1, hn1⟩⟩
  apply hx
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have key : ∀ i : Fin 2, ∀ n : ℤ, (n : ℚ) = c * toQ M x i → x i = 0 := by
    intro i n hn
    have hlt := ZMod.val_lt (x i)
    have e : (n : ℚ) * M = (c * (x i).val : ℕ) := by
      rw [hn, toQ]
      push_cast
      field_simp
    have e' : n * (M : ℤ) = ((c * (x i).val : ℕ) : ℤ) := by exact_mod_cast e
    have hd : (M : ℤ) ∣ ((c * (x i).val : ℕ) : ℤ) := ⟨n, by rw [← e', mul_comm]⟩
    have hd' : M ∣ c * (x i).val := by exact_mod_cast hd
    have hv : M ∣ (x i).val := (Nat.Coprime.symm hcM).dvd_of_dvd_mul_left hd'
    have hv0 : (x i).val = 0 := by
      rcases Nat.eq_zero_or_pos (x i).val with h | h
      · exact h
      · exact absurd (Nat.le_of_dvd h hv) (not_le.mpr hlt)
    exact (ZMod.val_eq_zero _).mp hv0
  funext i
  fin_cases i
  · exact key 0 n0 hn0
  · exact key 1 n1 hn1

/- English proof (translation)
Establish `h1 : v + a * M < (a + 1) * M` using `by nlinarith`. Establish `h2 : (a + 1) * M ≤ k * M` using `Nat.mul_le_mul_right _ ha`. Use linear arithmetic over natural numbers and integers.
-/
private theorem add_mul_lt_mul {k M a v : ℕ} (ha : a < k) (hv : v < M) : v + a * M < k * M := by
  have h1 : v + a * M < (a + 1) * M := by nlinarith
  have h2 : (a + 1) * M ≤ k * M := Nat.mul_le_mul_right _ ha
  omega

/- English proof (translation)
Use `show (ZMod.castHom _ (ZMod M) (x' i)).val = _`. Rewrite using `[ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]`.
-/
private theorem dn_val (k M : ℕ) [NeZero (k * M)] (x' : Row (k * M)) (i : Fin 2) :
    (dn k M x' i).val = (x' i).val % M := by
  show (ZMod.castHom _ (ZMod M) (x' i)).val = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

/- English proof (translation)
Use `haveI : NeZero (k * M) := ⟨hkM⟩`. Establish `h` using `ZMod.val_lt y`. Combine the linear relations using `[Nat.mul_comm k M]`.
-/
private theorem val_lt_mul_of_zmod_mul {k M : ℕ} (y : ZMod (k * M)) (hkM : k * M ≠ 0) : y.val < M * k := by
  haveI : NeZero (k * M) := ⟨hkM⟩
  have h := ZMod.val_lt y
  linarith [Nat.mul_comm k M]

/- English proof (translation)
Introduce `Ω _ _ _ ε X c k M _ hc h6 hcop x hx`. Establish `hkM : k * M ≠ 0` using `NeZero.ne _`. Establish `hk : 0 < k` using `Nat.pos_of_ne_zero (fun h => hkM (by simp [h]))`. Establish `hM : 0 < M` using `Nat.pos_of_ne_zero (fun h => hkM (by simp [h]))`. Use `haveI : NeZero M := ⟨hM.ne'⟩`.

Establish `hcM : c.Coprime M` using `Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hcop`. Establish `hck : c.Coprime k` using `Nat.Coprime.coprime_dvd_right (dvd_mul_right k M) hcop`. Establish `hMq : (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `hkq : (k : ℚ) ≠ 0` using `by exact_mod_cast hk.ne'`. Establish `split : ∀ x' : Row (k * M), dn k M x' = x → ∀ i : Fin 2, (x' i).val = (x i).val + (x' i).val / M * M`.

Introduce `x' hx' i`. Establish `h` using `dn_val k M x' i`. Rewrite `h` using `[hx']`. Rewrite using `[h, Nat.mod_add_div']`. Establish `qlt : ∀ x' : Row (k * M), ∀ i : Fin 2, (x' i).val / M < k` using `fun x' i => Nat.div_lt_of_lt_mul (val_lt_mul_of_zmod_mul (x' i) hkM)`.

Set `sel : ℕ × ℕ → Fin 2 → ℕ` to `fun p => ![p.1, p.2]`. Set `j : ℕ × ℕ → Row (k * M)` to `fun p i => (((x i).val + sel p i * M : ℕ) : ZMod (k * M))`. Establish `jval : ∀ p ∈ Finset.range k ×ˢ Finset.range k, ∀ i : Fin 2, (j p i).val = (x i).val + sel p i * M`. Introduce `p hp i`. Rewrite `hp` using `[Finset.mem_product, Finset.mem_range, Finset.mem_range]`.

Establish `hs : sel p i < k` using `by fin_cases i`. Conclude with `hp.1`. Conclude with `hp.2`. Use `show ((((x i).val + sel p i * M : ℕ)) : ZMod (k * M)).val = _`. Rewrite using `[ZMod.val_natCast]`.

Conclude with `Nat.mod_eq_of_lt (add_mul_lt_mul hs (ZMod.val_lt (x i)))`. Rewrite using `[sg, ← GlobalTheory.KZDist.siegel_distribution Ω ε X c k (toQ M x) (siegel_admissible_to_rat c M hc h6 hM hcM x hx) hk hck, ← Finset.prod_product']`. Use `Finset.prod_nbij' (fun x' => ((x' 0).val / M, (x' 1).val / M)) j ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x' _`. Simplify using `only [Finset.mem_product, Finset.mem_range]`.

Conclude with `⟨qlt x' 0, qlt x' 1⟩`. Introduce `p hp`. Rewrite using `[Finset.mem_filter]`. Use `⟨Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Apply `ZMod.val_injective` to reduce the goal to its premises. Rewrite using `[dn_val, jval p hp i, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (ZMod.val_lt (x i))]`. Introduce `x' hx'`. Rewrite `hx'` using `[Finset.mem_filter]`. Use function extensionality and compare the values at `i`.

Establish `e` using `split x' hx'.2 i`. Use `show ((((x i).val + sel _ i * M : ℕ)) : ZMod (k * M)) = x' i`. Apply the tactic sequence `have hsel : sel ((x' 0).val / M, (x' 1).val / M) i = (x' i).val / M := by fin_cases i <;> rfl`. Rewrite using `[hsel, ← e, ZMod.natCast_zmod_val]`. Introduce `p hp`.

Establish `h0` using `jval p hp 0`. Establish `h1` using `jval p hp 1`. Establish `v0` using `ZMod.val_lt (x 0)`. Establish `v1` using `ZMod.val_lt (x 1)`. Rewrite using `[h0, h1]`.

Use `ext`. Use `show ((x 0).val + p.1 * M) / M = p.1`. Rewrite using `[Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt v0, zero_add]`. Use `show ((x 1).val + p.2 * M) / M = p.2`. Rewrite using `[Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt v1, zero_add]`.

Introduce `x' hx'`. Rewrite `hx'` using `[Finset.mem_filter]`. Establish `e0` using `split x' hx'.2 0`. Establish `e1` using `split x' hx'.2 1`. Use `show siegel X c (toQ (k * M) x') = _`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Use `show ((x' 0).val : ℚ) / ((k * M : ℕ) : ℚ) = (toQ M x 0 + (((x' 0).val / M : ℕ) : ℚ)) / k`. Rewrite using `[toQ]`.

Generalize the expression as in `(x' 0).val / M = q at e0 ⊢`. Rewrite using `[e0]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use `show ((x' 1).val : ℚ) / ((k * M : ℕ) : ℚ) = (toQ M x 1 + (((x' 1).val / M : ℕ) : ℚ)) / k`.

Rewrite using `[toQ]`. Generalize the expression as in `(x' 1).val / M = q at e1 ⊢`. Rewrite using `[e1]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.V.Z.Kato.Sym.sgDist :
    UpperTheory.V.Z.Kato.Sym.SgDist := by
  classical
  intro Ω _ _ _ ε X c k M _ hc h6 hcop x hx
  have hkM : k * M ≠ 0 := NeZero.ne _
  have hk : 0 < k := Nat.pos_of_ne_zero (fun h => hkM (by simp [h]))
  have hM : 0 < M := Nat.pos_of_ne_zero (fun h => hkM (by simp [h]))
  haveI : NeZero M := ⟨hM.ne'⟩
  have hcM : c.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hcop
  have hck : c.Coprime k := Nat.Coprime.coprime_dvd_right (dvd_mul_right k M) hcop
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have split : ∀ x' : Row (k * M), dn k M x' = x → ∀ i : Fin 2,
      (x' i).val = (x i).val + (x' i).val / M * M := by
    intro x' hx' i
    have h := dn_val k M x' i
    rw [hx'] at h
    rw [h, Nat.mod_add_div']
  have qlt : ∀ x' : Row (k * M), ∀ i : Fin 2, (x' i).val / M < k := fun x' i =>
    Nat.div_lt_of_lt_mul (val_lt_mul_of_zmod_mul (x' i) hkM)
  let sel : ℕ × ℕ → Fin 2 → ℕ := fun p => ![p.1, p.2]
  let j : ℕ × ℕ → Row (k * M) := fun p i => (((x i).val + sel p i * M : ℕ) : ZMod (k * M))
  have jval : ∀ p ∈ Finset.range k ×ˢ Finset.range k, ∀ i : Fin 2,
      (j p i).val = (x i).val + sel p i * M := by
    intro p hp i
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    have hs : sel p i < k := by
      fin_cases i
      · exact hp.1
      · exact hp.2
    show ((((x i).val + sel p i * M : ℕ)) : ZMod (k * M)).val = _
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (add_mul_lt_mul hs (ZMod.val_lt (x i)))
  rw [sg, ← GlobalTheory.KZDist.siegel_distribution Ω ε X c k (toQ M x) (siegel_admissible_to_rat c M hc h6 hM hcM x hx) hk hck,
    ← Finset.prod_product']
  refine Finset.prod_nbij' (fun x' => ((x' 0).val / M, (x' 1).val / M)) j ?_ ?_ ?_ ?_ ?_
  · intro x' _
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨qlt x' 0, qlt x' 1⟩
  · intro p hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    funext i
    apply ZMod.val_injective
    rw [dn_val, jval p hp i, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (ZMod.val_lt (x i))]
  · intro x' hx'
    rw [Finset.mem_filter] at hx'
    funext i
    have e := split x' hx'.2 i
    show ((((x i).val + sel _ i * M : ℕ)) : ZMod (k * M)) = x' i
    have hsel : sel ((x' 0).val / M, (x' 1).val / M) i = (x' i).val / M := by
      fin_cases i <;> rfl
    rw [hsel, ← e, ZMod.natCast_zmod_val]
  · intro p hp
    have h0 := jval p hp 0
    have h1 := jval p hp 1
    have v0 := ZMod.val_lt (x 0)
    have v1 := ZMod.val_lt (x 1)
    rw [h0, h1]
    ext
    · show ((x 0).val + p.1 * M) / M = p.1
      rw [Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt v0, zero_add]
    · show ((x 1).val + p.2 * M) / M = p.2
      rw [Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt v1, zero_add]
  · intro x' hx'
    rw [Finset.mem_filter] at hx'
    have e0 := split x' hx'.2 0
    have e1 := split x' hx'.2 1
    show siegel X c (toQ (k * M) x') = _
    congr 1
    funext i
    fin_cases i
    · show ((x' 0).val : ℚ) / ((k * M : ℕ) : ℚ) = (toQ M x 0 + (((x' 0).val / M : ℕ) : ℚ)) / k
      rw [toQ]
      generalize (x' 0).val / M = q at e0 ⊢
      rw [e0]
      push_cast
      field_simp
    · show ((x' 1).val : ℚ) / ((k * M : ℕ) : ℚ) = (toQ M x 1 + (((x' 1).val / M : ℕ) : ℚ)) / k
      rw [toQ]
      generalize (x' 1).val / M = q at e1 ⊢
      rw [e1]
      push_cast
      field_simp
