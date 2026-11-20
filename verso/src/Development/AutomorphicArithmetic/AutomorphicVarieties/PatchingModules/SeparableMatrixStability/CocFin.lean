import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `G R _ _ _ _ _ n ρ hfg h1 hmul hρ`. Take `⟨s, hs, hden⟩` from `hfg`. Use `haveI : Finite s := hs.to_subtype`. Establish `hinv : ∀ g, ρ g⁻¹ * ρ g = 1` using `fun g => by rw [← hmul, inv_mul_cancel, h1]`. Establish `hinv' : ∀ g, ρ g * ρ g⁻¹ = 1` using `fun g => by rw [← hmul, mul_inv_cancel, h1]`.

Establish `hz1 : ∀ z : G → Matrix (Fin n) (Fin n) R, (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) → z 1 = 0`. Introduce `z hz`. Use `hz 1 1` as an intermediate fact. Simplify `this` using `[h1]`. Establish `hzinv : ∀ z : G → Matrix (Fin n) (Fin n) R, (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) → ∀ g, z g⁻¹ = ρ g⁻¹ * (-z g) * ρ g`.

Introduce `z hz g`. Establish `e` using `hz g g⁻¹`. Rewrite `e` using `[mul_inv_cancel, hz1 z hz]`. Establish `e2 : ρ g * z g⁻¹ * ρ g⁻¹ = -z g` using `eq_neg_of_add_eq_zero_right e.symm`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hinv, Matrix.mul_one, ← Matrix.mul_assoc, hinv, Matrix.one_mul]`. Use `_ = ρ g⁻¹ * (-z g) * ρ g := by rw [e2]`. Apply `Set.Finite.of_finite_image (f := fun z : G → Matrix (Fin n) (Fin n) R => fun x : s => z x) (Set.toFinite _)` to reduce the goal to its premises. Introduce and unpack `z ⟨hzl, hz⟩ z' ⟨hzl', hz'⟩ he`.

Set `H : Subgroup G` to `{ carrier := {g | z g = z' g} mul_mem' := fun {a b} ha hb => by`. Express the relevant statement in the definitionally equal form `z (a * b) = z' (a * b)`. Express the relevant statement in the definitionally equal form `z a = z' a at ha`. Express the relevant statement in the definitionally equal form `z b = z' b at hb`. Rewrite using `[hz, hz', ha, hb]`.

Use the proof step `one_mem' := by`. Express the relevant statement in the definitionally equal form `z 1 = z' 1`. Rewrite using `[hz1 z hz, hz1 z' hz']`. Use the proof step `inv_mem' := fun {a} ha => by`. Express the relevant statement in the definitionally equal form `z a = z' a at ha`.

Express the relevant statement in the definitionally equal form `z a⁻¹ = z' a⁻¹`. Rewrite using `[hzinv z hz, hzinv z' hz', ha] }`. Establish `hsH : Subgroup.closure s ≤ H` using `(Subgroup.closure_le H).2 fun x hx => congrFun he ⟨x, hx⟩`. Establish `hcl : IsClosed (H : Set G)`. Establish `hd` using `hzl.comp₂ hzl' (fun a b => a - b)`.

Establish `hc` using `hd.isClosed_fiber 0`. Use `hc using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Conclude with `sub_eq_zero.symm`. Establish `hU : (H : Set G) = Set.univ`.

Apply `Set.eq_univ_of_univ_subset` to reduce the goal to its premises. Rewrite using `[← hden.closure_eq]`. Conclude with `closure_minimal (fun x hx => hsH hx) hcl`. Use function extensionality and compare the values at `g`. Establish `hg : g ∈ (H : Set G)` using `hU ▸ Set.mem_univ g`.

Conclude with `hg`.
-/
theorem UpperTheory.V.Pa.coc_fin :
    ∀ (G R : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CommRing R] [Finite R] (n : ℕ) (ρ : G → Matrix (Fin n) (Fin n) R), TopFG G → ρ 1 = 1 → (∀ g h, ρ (g * h) = ρ g * ρ h) → IsLocallyConstant ρ → {z : G → Matrix (Fin n) (Fin n) R | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹}.Finite := by
  intro G R _ _ _ _ _ n ρ hfg h1 hmul hρ
  obtain ⟨s, hs, hden⟩ := hfg
  haveI : Finite s := hs.to_subtype
  have hinv : ∀ g, ρ g⁻¹ * ρ g = 1 := fun g => by rw [← hmul, inv_mul_cancel, h1]
  have hinv' : ∀ g, ρ g * ρ g⁻¹ = 1 := fun g => by rw [← hmul, mul_inv_cancel, h1]
  have hz1 : ∀ z : G → Matrix (Fin n) (Fin n) R, (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) → z 1 = 0 := by
    intro z hz
    have := hz 1 1
    simpa [h1] using this
  have hzinv : ∀ z : G → Matrix (Fin n) (Fin n) R, (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) →
      ∀ g, z g⁻¹ = ρ g⁻¹ * (-z g) * ρ g := by
    intro z hz g
    have e := hz g g⁻¹
    rw [mul_inv_cancel, hz1 z hz] at e
    have e2 : ρ g * z g⁻¹ * ρ g⁻¹ = -z g := eq_neg_of_add_eq_zero_right e.symm
    calc z g⁻¹ = ρ g⁻¹ * (ρ g * z g⁻¹ * ρ g⁻¹) * ρ g := by
          simp only [Matrix.mul_assoc]
          rw [hinv, Matrix.mul_one, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
      _ = ρ g⁻¹ * (-z g) * ρ g := by rw [e2]
  apply Set.Finite.of_finite_image (f := fun z : G → Matrix (Fin n) (Fin n) R => fun x : s => z x)
    (Set.toFinite _)
  rintro z ⟨hzl, hz⟩ z' ⟨hzl', hz'⟩ he
  let H : Subgroup G :=
    { carrier := {g | z g = z' g}
      mul_mem' := fun {a b} ha hb => by
        change z (a * b) = z' (a * b)
        change z a = z' a at ha
        change z b = z' b at hb
        rw [hz, hz', ha, hb]
      one_mem' := by
        change z 1 = z' 1
        rw [hz1 z hz, hz1 z' hz']
      inv_mem' := fun {a} ha => by
        change z a = z' a at ha
        change z a⁻¹ = z' a⁻¹
        rw [hzinv z hz, hzinv z' hz', ha] }
  have hsH : Subgroup.closure s ≤ H := (Subgroup.closure_le H).2 fun x hx => congrFun he ⟨x, hx⟩
  have hcl : IsClosed (H : Set G) := by
    have hd := hzl.comp₂ hzl' (fun a b => a - b)
    have hc := hd.isClosed_fiber 0
    convert hc using 1
    ext g
    exact sub_eq_zero.symm
  have hU : (H : Set G) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hden.closure_eq]
    exact closure_minimal (fun x hx => hsH hx) hcl
  funext g
  have hg : g ∈ (H : Set G) := hU ▸ Set.mem_univ g
  exact hg
