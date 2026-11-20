import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open UpperTheory.V.Af.BA in
/- English proof (translation)
Unfold `UpperTheory.V.Af.BA.DimBdd`. Introduce `Γ I _ _ K hfin hstab0`. Establish `hre : ∀ {p q : ℕ} (f : Fin (p+1) → Fin (q+1)) (t : K.Tup q) (g : Γ), g • t = t → g • K.re f t = K.re f t`. Introduce `p q f t g hg`. Use `show K.re f (g • t) = K.re f t`.

Rewrite using `[hg]`. Establish `hst : ∀ (p : ℕ) (t : K.Tup p), Finite ↥(MulAction.stabilizer Γ t)`. Introduce `p t`. Use `haveI := hstab0 (K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t)`. Establish `hle : MulAction.stabilizer Γ t ≤ MulAction.stabilizer Γ (K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t)` using `fun g hg => hre _ t g hg`.

Conclude with `Finite.of_injective _ (Subgroup.inclusion_injective hle)`. Use `⟨hst, ?_⟩` and prove the remaining obligations. Take `⟨R, hRfin, hR⟩` from `hfin`. Use `haveI : Finite ↥R := hRfin.to_subtype`. Set `V : K.Tup 1 → K.Tup 0` to `fun r => K.re (fun _ : Fin 1 => (0 : Fin 2)) r`.

Use `haveI : ∀ r : ↥R, Finite ↥(MulAction.stabilizer Γ (V r.1)) := fun r => hstab0 _`. Use `⟨Nat.card (Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1))), ?_⟩` and prove the remaining obligations. Introduce `p hp t ht`. Set `v : K.Tup 0` to `K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t`. Set `e : Fin (p+1) → K.Tup 1` to `fun j => K.re (![0, j] : Fin 2 → Fin (p+1)) t`.

Establish `hev : ∀ j, V (e j) = v` using `fun j => Subtype.ext (funext fun _ => rfl)`. Set `k : ↥R → Γ` to `fun r => if h : ∃ g : Γ, g • v = V r.1 then Classical.choose h else 1`. Set `gsel : Fin (p+1) → Γ` to `fun j => Classical.choose (hR (e j))`. Establish `hgsel : ∀ j, gsel j • e j ∈ R` using `fun j => Classical.choose_spec (hR (e j))`. Set `rsel : Fin (p+1) → ↥R` to `fun j => ⟨gsel j • e j, hgsel j⟩`.

Establish `hgv : ∀ j, gsel j • v = V (rsel j).1`. Introduce `j`. Use `show gsel j • v = gsel j • V (e j)`. Rewrite using `[hev j]`. Establish `hk : ∀ j, k (rsel j) • v = V (rsel j).1`.

Introduce `j`. Establish `hex : ∃ g : Γ, g • v = V (rsel j).1` using `⟨gsel j, hgv j⟩`. Establish `hkj : k (rsel j) = Classical.choose hex` using `dif_pos hex`. Rewrite using `[hkj]`. Conclude with `Classical.choose_spec hex`.

Establish `hmem : ∀ j, gsel j * (k (rsel j))⁻¹ ∈ MulAction.stabilizer Γ (V (rsel j).1)`. Introduce `j`. Rewrite using `[MulAction.mem_stabilizer_iff, mul_smul]`. Establish `h1 : (k (rsel j))⁻¹ • V (rsel j).1 = v`. Rewrite using `[inv_smul_eq_iff]`.

Conclude with `(hk j).symm`. Rewrite using `[h1, hgv j]`. Set `φ : Fin (p+1) → Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1))` to `fun j => ⟨rsel j, ⟨gsel j * (k (rsel j))⁻¹, hmem j⟩⟩`. Set `ψ : (Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1))) → K.Tup 1` to `fun x => ((x.2 : Γ) * k x.1)⁻¹ • x.1.1`. Establish `hψ : ∀ j, ψ (φ j) = e j`.

Introduce `j`. Use `show ((gsel j * (k (rsel j))⁻¹) * k (rsel j))⁻¹ • (gsel j • e j) = e j`. Rewrite using `[inv_mul_cancel_right, inv_smul_smul]`. Establish `hinj : Function.Injective φ`. Introduce `j j' hjj`.

Apply `ht` to reduce the goal to its premises. Establish `h1 : e j = e j'` using `by rw [← hψ j, ← hψ j', hjj]`. Establish `h2` using `congrArg (fun x : K.Tup 1 => x.1 1) h1`. Conclude with `h2`. Establish `hcard` using `Nat.card_le_card_of_injective φ hinj`.

Rewrite `hcard` using `[Nat.card_eq_fintype_card, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.adelic_rep_dimension_bounded :
    UpperTheory.V.Af.BA.DimBdd := by
  classical
  unfold UpperTheory.V.Af.BA.DimBdd
  intro Γ I _ _ K hfin hstab0
  have hre : ∀ {p q : ℕ} (f : Fin (p+1) → Fin (q+1)) (t : K.Tup q) (g : Γ),
      g • t = t → g • K.re f t = K.re f t := by
    intro p q f t g hg
    show K.re f (g • t) = K.re f t
    rw [hg]
  have hst : ∀ (p : ℕ) (t : K.Tup p), Finite ↥(MulAction.stabilizer Γ t) := by
    intro p t
    haveI := hstab0 (K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t)
    have hle : MulAction.stabilizer Γ t ≤
        MulAction.stabilizer Γ (K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t) :=
      fun g hg => hre _ t g hg
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  refine ⟨hst, ?_⟩
  obtain ⟨R, hRfin, hR⟩ := hfin
  haveI : Finite ↥R := hRfin.to_subtype
  let V : K.Tup 1 → K.Tup 0 := fun r => K.re (fun _ : Fin 1 => (0 : Fin 2)) r
  haveI : ∀ r : ↥R, Finite ↥(MulAction.stabilizer Γ (V r.1)) := fun r => hstab0 _
  refine ⟨Nat.card (Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1))), ?_⟩
  intro p hp t ht
  let v : K.Tup 0 := K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t
  let e : Fin (p+1) → K.Tup 1 := fun j => K.re (![0, j] : Fin 2 → Fin (p+1)) t
  have hev : ∀ j, V (e j) = v := fun j => Subtype.ext (funext fun _ => rfl)
  let k : ↥R → Γ := fun r => if h : ∃ g : Γ, g • v = V r.1 then Classical.choose h else 1
  let gsel : Fin (p+1) → Γ := fun j => Classical.choose (hR (e j))
  have hgsel : ∀ j, gsel j • e j ∈ R := fun j => Classical.choose_spec (hR (e j))
  let rsel : Fin (p+1) → ↥R := fun j => ⟨gsel j • e j, hgsel j⟩
  have hgv : ∀ j, gsel j • v = V (rsel j).1 := by
    intro j
    show gsel j • v = gsel j • V (e j)
    rw [hev j]
  have hk : ∀ j, k (rsel j) • v = V (rsel j).1 := by
    intro j
    have hex : ∃ g : Γ, g • v = V (rsel j).1 := ⟨gsel j, hgv j⟩
    have hkj : k (rsel j) = Classical.choose hex := dif_pos hex
    rw [hkj]
    exact Classical.choose_spec hex
  have hmem : ∀ j, gsel j * (k (rsel j))⁻¹ ∈ MulAction.stabilizer Γ (V (rsel j).1) := by
    intro j
    rw [MulAction.mem_stabilizer_iff, mul_smul]
    have h1 : (k (rsel j))⁻¹ • V (rsel j).1 = v := by
      rw [inv_smul_eq_iff]
      exact (hk j).symm
    rw [h1, hgv j]
  let φ : Fin (p+1) → Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1)) :=
    fun j => ⟨rsel j, ⟨gsel j * (k (rsel j))⁻¹, hmem j⟩⟩
  let ψ : (Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1))) → K.Tup 1 :=
    fun x => ((x.2 : Γ) * k x.1)⁻¹ • x.1.1
  have hψ : ∀ j, ψ (φ j) = e j := by
    intro j
    show ((gsel j * (k (rsel j))⁻¹) * k (rsel j))⁻¹ • (gsel j • e j) = e j
    rw [inv_mul_cancel_right, inv_smul_smul]
  have hinj : Function.Injective φ := by
    intro j j' hjj
    apply ht
    have h1 : e j = e j' := by rw [← hψ j, ← hψ j', hjj]
    have h2 := congrArg (fun x : K.Tup 1 => x.1 1) h1
    exact h2
  have hcard := Nat.card_le_card_of_injective φ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  omega
