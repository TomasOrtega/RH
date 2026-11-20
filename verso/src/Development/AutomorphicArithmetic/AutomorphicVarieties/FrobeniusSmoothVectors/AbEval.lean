import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AbEval

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Fr

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Ra1.ab_eval r`.
-/
private theorem ab_eval {k X : Type} [Field k] [Inhabited X] (r : ℕ) :
    ∀ H : Submodule k (X → k), Module.Finite k H → Module.finrank k H ≤ r →
      ∃ t : Fin r → X, ∀ φ ∈ H, (∀ a, φ (t a) = 0) → φ = 0 :=
  _root_.UpperTheory.Reformulated.B.Ra1.ab_eval r

/- English proof (translation)
The claim follows from `haveI : Module.Free k H := Module.Free.of_divisionRing k H ab_eval r H (Module.rank_lt_aleph0_iff.1 (hr.trans_lt Cardinal.natCast_lt_aleph0)) (Module.finrank_le_of_rank_le hr)`.
-/
private theorem ab_eval' {k X : Type} [Field k] [Inhabited X] (r : ℕ) (H : Submodule k (X → k))
    (hr : Module.rank k H ≤ r) : ∃ t : Fin r → X, ∀ φ ∈ H, (∀ a, φ (t a) = 0) → φ = 0 :=
  haveI : Module.Free k H := Module.Free.of_divisionRing k H
  ab_eval r H (Module.rank_lt_aleph0_iff.1 (hr.trans_lt Cardinal.natCast_lt_aleph0)) (Module.finrank_le_of_rank_le hr)

/- English proof (translation)
Take `⟨n, hn0, hn⟩` from `hB.nontrivial_iff_card.1 inferInstance`. Take `⟨n, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hn0.ne'`. Establish `hl : l.Prime` using `Fact.out`. Take `⟨K, hK⟩` from `Sylow.exists_subgroup_card_pow_prime (G := B) l (n := n) (hn ▸ pow_dvd_pow l n.le_succ)`. Establish `hq : Nat.card (B ⧸ K) = l`.

Use `Subgroup.card_eq_card_quotient_mul_card_subgroup K` as an intermediate fact. Rewrite `this` using `[hn, hK, pow_succ']`. Conclude with `(Nat.eq_of_mul_eq_mul_right (pow_pos hl.pos n) this).symm`. Establish `hz : Nat.card (Multiplicative (ZMod l)) = l` using `by simp`. Set `e` to `mulEquivOfPrimeCardEq hq hz`.

Set `j : Multiplicative (ZMod l) →* Multiplicative k` to `AddMonoidHom.toMultiplicative (ZMod.castHom (dvd_refl l) k).toAddMonoidHom`. Establish `hj : Function.Injective j` using `(ZMod.castHom (dvd_refl l) k).injective`. Use `haveI : Nontrivial (B ⧸ K) := Finite.one_lt_card_iff_nontrivial.1 (hq.symm ▸ hl.one_lt)`. Take `⟨q, hq1⟩` from `exists_ne (1 : B ⧸ K)`. Take `⟨b, rfl⟩` from `QuotientGroup.mk_surjective q`.

Use `⟨j.comp (e.toMonoidHom.comp (QuotientGroup.mk' K)), b, fun h => hq1 ?_⟩` and prove the remaining obligations. Conclude with `e.injective (hj (h.trans (by simp)))`.
-/
private theorem ab_char {l : ℕ} [Fact l.Prime] (k : Type) [Field k] [CharP k l] {B : Type} [CommGroup B] [Finite B]
    [Nontrivial B] (hB : IsPGroup l B) : ∃ ψ : B →* Multiplicative k, ∃ b, ψ b ≠ 1 := by
  obtain ⟨n, hn0, hn⟩ := hB.nontrivial_iff_card.1 inferInstance
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0.ne'
  have hl : l.Prime := Fact.out
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) l (n := n) (hn ▸ pow_dvd_pow l n.le_succ)
  have hq : Nat.card (B ⧸ K) = l := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [hn, hK, pow_succ'] at this
    exact (Nat.eq_of_mul_eq_mul_right (pow_pos hl.pos n) this).symm
  have hz : Nat.card (Multiplicative (ZMod l)) = l := by simp
  let e := mulEquivOfPrimeCardEq hq hz
  let j : Multiplicative (ZMod l) →* Multiplicative k :=
    AddMonoidHom.toMultiplicative (ZMod.castHom (dvd_refl l) k).toAddMonoidHom
  have hj : Function.Injective j := (ZMod.castHom (dvd_refl l) k).injective
  haveI : Nontrivial (B ⧸ K) := Finite.one_lt_card_iff_nontrivial.1 (hq.symm ▸ hl.one_lt)
  obtain ⟨q, hq1⟩ := exists_ne (1 : B ⧸ K)
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨j.comp (e.toMonoidHom.comp (QuotientGroup.mk' K)), b, fun h => hq1 ?_⟩
  exact e.injective (hj (h.trans (by simp)))

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}

/- English proof (translation)
Set `L : H1C F.loc (chRep (1 : F.Γ →* kˣ)) (fun _ => ⊤) →ₗ[k] (F.Γ → k)` to `Submodule.liftQ _ ((LinearMap.fst k _ _).comp (Submodule.subtype _)) (by`. Introduce and unpack `x ⟨X, h, -⟩`. Use function extensionality and compare the values at `s`. Simplify using `using h s)`. Establish `hr : Module.rank k (LinearMap.range L) ≤ ((1 + C₀ : ℕ) : Cardinal)` using `(rank_range_le L).trans (by exact_mod_cast hF.h1)`.

Use `haveI : Inhabited F.Γ := ⟨1⟩`. Take `⟨t, ht⟩` from `ab_eval' (1 + C₀) (LinearMap.range L) hr`. Use `⟨t, fun A _ _ hA φ ho hz g => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hg`. Use `haveI : Nontrivial φ.range := ⟨⟨φ.rangeRestrict g, 1, fun e => hg (congrArg Subtype.val e)⟩⟩`.

Take `⟨ψ, b, hb⟩` from `ab_char k (hA.to_subgroup φ.range)`. Take `⟨x, rfl⟩` from `φ.rangeRestrict_surjective b`. Set `f : F.Γ → k` to `fun s => (ψ (φ.rangeRestrict s)).toAdd`. Establish `hlc : IsLocallyConstant f`. Use `(IsLocallyConstant.iff_exists_open _).2 fun s => ⟨(fun y => s⁻¹ * y) ⁻¹' φ.ker, ho.preimage (by fun_prop), by simp, fun y hy => ?_⟩` and prove the remaining obligations.

Establish `: φ.rangeRestrict y = φ.rangeRestrict s`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h : φ (s⁻¹ * y) = 1` using `hy`. Rewrite `h` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `h.symm`.

Simplify using `only [f, this]`. Establish `hm : f ∈ LinearMap.range L` using `⟨Submodule.Quotient.mk ⟨(f, 0), hlc, fun s u => by simp [f], fun _ _ => trivial⟩, rfl⟩`. Use `ht f hm fun a => by` as an intermediate fact. Establish `: φ.rangeRestrict (t a) = 1` using `Subtype.ext (hz a)`. Simplify using `[f, this]`.

Conclude with `hb (congrFun this x)`.
-/
private theorem ab_plus (hF : F.Ok C₀) : ∃ t : Fin (1 + C₀) → F.Γ,
    ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ φ : F.Γ →* A, IsOpen (φ.ker : Set F.Γ) →
      (∀ a, φ (t a) = 1) → ∀ g, φ g = 1 := by
  let L : H1C F.loc (chRep (1 : F.Γ →* kˣ)) (fun _ => ⊤) →ₗ[k] (F.Γ → k) :=
    Submodule.liftQ _ ((LinearMap.fst k _ _).comp (Submodule.subtype _)) (by
      rintro x ⟨X, h, -⟩
      funext s
      simpa using h s)
  have hr : Module.rank k (LinearMap.range L) ≤ ((1 + C₀ : ℕ) : Cardinal) :=
    (rank_range_le L).trans (by exact_mod_cast hF.h1)
  haveI : Inhabited F.Γ := ⟨1⟩
  obtain ⟨t, ht⟩ := ab_eval' (1 + C₀) (LinearMap.range L) hr
  refine ⟨t, fun A _ _ hA φ ho hz g => ?_⟩
  by_contra hg
  haveI : Nontrivial φ.range := ⟨⟨φ.rangeRestrict g, 1, fun e => hg (congrArg Subtype.val e)⟩⟩
  obtain ⟨ψ, b, hb⟩ := ab_char k (hA.to_subgroup φ.range)
  obtain ⟨x, rfl⟩ := φ.rangeRestrict_surjective b
  let f : F.Γ → k := fun s => (ψ (φ.rangeRestrict s)).toAdd
  have hlc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun s => ⟨(fun y => s⁻¹ * y) ⁻¹' φ.ker, ho.preimage (by fun_prop),
      by simp, fun y hy => ?_⟩
    have : φ.rangeRestrict y = φ.rangeRestrict s := by
      apply Subtype.ext
      have h : φ (s⁻¹ * y) = 1 := hy
      rw [map_mul, map_inv, inv_mul_eq_one] at h
      exact h.symm
    simp only [f, this]
  have hm : f ∈ LinearMap.range L :=
    ⟨Submodule.Quotient.mk ⟨(f, 0), hlc, fun s u => by simp [f], fun _ _ => trivial⟩, rfl⟩
  have := ht f hm fun a => by
    have : φ.rangeRestrict (t a) = 1 := Subtype.ext (hz a)
    simp [f, this]
  exact hb (congrFun this x)

/- English proof (translation)
Use `choose u a₀ hu _ hgen using hF.gen`. Take `⟨h, h0, hcl⟩` from `hF.cl`. Set `e : (Σ v, Fin (F.dv v)) ≃ Fin F.d` to `Fintype.equivFinOfCardEq (by simp [Frame.d])`. Use `⟨fun a => F.loc0 (e.symm a).1 (u _ (e.symm a).2), h, h0, fun a => ⟨_, _, (hu _ _).1, (hu _ _).2, rfl⟩, fun A _ _ hA χ ho hs hz => hcl A hA χ ho ?_⟩` and prove the remaining obligations. Establish `key : ∀ v, ∀ g ∈ F.Iv v, χ (F.loc0 v g) = 1` using `fun v => hgen v A hA (χ.comp (F.loc0 v)) (ho.preimage (hF.loc_cont v)) fun a => by`.

Use `hz (e ⟨v, a⟩)` as an intermediate fact. Use `beta_reduce at this`. Rewrite `this` using `[e.symm_apply_apply]`. Conclude with `this`. Introduce and unpack `⟨v, _ | _⟩ g hg`.

Conclude with `key v g hg`. Use `hs (F.loc0 v g)⁻¹` as an intermediate fact. Rewrite `this` using `[Frame.star, inv_inv, map_inv, key v g hg, inv_one]`. Conclude with `this`.
-/
private theorem ab_minus (hF : F.Ok C₀) : ∃ (s' : Fin F.d → F.G0) (h : ℕ), h ≠ 0 ∧
    (∀ a, ∃ v g, g ∈ F.Iv v ∧ F.Ψ (F.loc v g) = 1 ∧ s' a = F.loc0 v g) ∧
    ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.G0 →* A, IsOpen (χ.ker : Set F.G0) →
      (∀ g, χ (F.star g) = χ g) → (∀ a, χ (s' a) = 1) → ∀ g, χ g ^ h = 1 := by
  choose u a₀ hu _ hgen using hF.gen
  obtain ⟨h, h0, hcl⟩ := hF.cl
  let e : (Σ v, Fin (F.dv v)) ≃ Fin F.d := Fintype.equivFinOfCardEq (by simp [Frame.d])
  refine ⟨fun a => F.loc0 (e.symm a).1 (u _ (e.symm a).2), h, h0,
    fun a => ⟨_, _, (hu _ _).1, (hu _ _).2, rfl⟩, fun A _ _ hA χ ho hs hz => hcl A hA χ ho ?_⟩
  have key : ∀ v, ∀ g ∈ F.Iv v, χ (F.loc0 v g) = 1 := fun v =>
    hgen v A hA (χ.comp (F.loc0 v)) (ho.preimage (hF.loc_cont v)) fun a => by
      have := hz (e ⟨v, a⟩)
      beta_reduce at this
      rw [e.symm_apply_apply] at this
      exact this
  rintro ⟨v, _ | _⟩ g hg
  · exact key v g hg
  · have := hs (F.loc0 v g)⁻¹
    rw [Frame.star, inv_inv, map_inv, key v g hg, inv_one] at this
    exact this

/- English proof (translation)
Establish `hc : ∀ γ : F.Γ, γ ∉ F.del.ker → γ * F.c ∈ F.del.ker` using `fun γ h => by`. Rewrite `h`, the goal using `[MonoidHom.mem_ker]`. Rewrite using `[map_mul, hF.del_c, (Int.units_eq_one_or _).resolve_left h]`. Simplify using the standard rewrite rules. Establish `hci : F.c⁻¹ = F.c` using `inv_eq_of_mul_eq_one_right hF.c_sq`.

Establish `hcj : ∀ g : F.G0, (F.conj g : F.Γ) = F.c * g * F.c` using `fun g => by show F.c * g * F.c⁻¹ = _`. Rewrite using `[hci]`. Set `π : F.Γ → F.G0` to `fun γ => if h : γ ∈ F.del.ker then ⟨γ, h⟩ else ⟨γ * F.c, hc γ h⟩`. Establish `p1 : ∀ γ, γ ∈ F.del.ker → (π γ : F.Γ) = γ` using `fun γ h => by simp only [π, dif_pos h]`. Establish `p2 : ∀ γ, γ ∉ F.del.ker → (π γ : F.Γ) = γ * F.c` using `fun γ h => by simp only [π, dif_neg h]`.

Use `⟨π, fun g => Subtype.ext (p1 g g.2), fun A _ χ hχ => ⟨MonoidHom.mk' (fun γ => χ (π γ)) fun a b => ?_, fun _ => rfl⟩⟩` and prove the remaining obligations. Distinguish the cases in `ha : a ∈ F.del.ker`. Rewrite using `[← map_mul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Distinguish the cases in `hb : b ∈ F.del.ker`. Rewrite using `[Subgroup.coe_mul, p1 _ ha, p1 _ hb, p1 _ (mul_mem ha hb)]`. Rewrite using `[Subgroup.coe_mul, p1 _ ha, p2 _ hb, p2 _ fun h => hb ((Subgroup.mul_mem_cancel_left _ ha).1 h), mul_assoc]`. Use `show χ _ = χ _ * χ _`. Rewrite using `[← hχ (π b), ← map_mul]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Distinguish the cases in `hb : b ∈ F.del.ker`. Rewrite using `[Subgroup.coe_mul, hcj, p2 _ ha, p1 _ hb, p2 _ fun h => ha ((Subgroup.mul_mem_cancel_right _ hb).1 h)]`. Simplify using `only [mul_assoc]`.

Rewrite using `[← mul_assoc F.c F.c, hF.c_sq, one_mul]`. Establish `hab : a * b ∈ F.del.ker`. Rewrite `ha`, `hb`, the goal using `[MonoidHom.mem_ker]`. Rewrite using `[map_mul, (Int.units_eq_one_or _).resolve_left ha, (Int.units_eq_one_or _).resolve_left hb]`. Simplify using the standard rewrite rules.

Rewrite using `[Subgroup.coe_mul, hcj, p2 _ ha, p2 _ hb, p1 _ hab]`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc F.c F.c, hF.c_sq, one_mul, mul_one]`.
-/
private theorem ab_ext (hF : F.Ok C₀) : ∃ π : F.Γ → F.G0, (∀ g : F.G0, π g = g) ∧
    ∀ (A : Type) [CommGroup A] (χ : F.G0 →* A), (∀ g, χ (F.conj g) = χ g) → ∃ φ : F.Γ →* A, ∀ γ, φ γ = χ (π γ) := by
  classical
  have hc : ∀ γ : F.Γ, γ ∉ F.del.ker → γ * F.c ∈ F.del.ker := fun γ h => by
    rw [MonoidHom.mem_ker] at h ⊢
    rw [map_mul, hF.del_c, (Int.units_eq_one_or _).resolve_left h]; simp
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
  have hcj : ∀ g : F.G0, (F.conj g : F.Γ) = F.c * g * F.c := fun g => by
    show F.c * g * F.c⁻¹ = _
    rw [hci]
  let π : F.Γ → F.G0 := fun γ => if h : γ ∈ F.del.ker then ⟨γ, h⟩ else ⟨γ * F.c, hc γ h⟩
  have p1 : ∀ γ, γ ∈ F.del.ker → (π γ : F.Γ) = γ := fun γ h => by simp only [π, dif_pos h]
  have p2 : ∀ γ, γ ∉ F.del.ker → (π γ : F.Γ) = γ * F.c := fun γ h => by simp only [π, dif_neg h]
  refine ⟨π, fun g => Subtype.ext (p1 g g.2), fun A _ χ hχ => ⟨MonoidHom.mk' (fun γ => χ (π γ)) fun a b => ?_, fun _ => rfl⟩⟩
  by_cases ha : a ∈ F.del.ker
  · rw [← map_mul]
    congr 1
    apply Subtype.ext
    by_cases hb : b ∈ F.del.ker
    · rw [Subgroup.coe_mul, p1 _ ha, p1 _ hb, p1 _ (mul_mem ha hb)]
    · rw [Subgroup.coe_mul, p1 _ ha, p2 _ hb, p2 _ fun h => hb ((Subgroup.mul_mem_cancel_left _ ha).1 h), mul_assoc]
  · show χ _ = χ _ * χ _
    rw [← hχ (π b), ← map_mul]
    congr 1
    apply Subtype.ext
    by_cases hb : b ∈ F.del.ker
    · rw [Subgroup.coe_mul, hcj, p2 _ ha, p1 _ hb, p2 _ fun h => ha ((Subgroup.mul_mem_cancel_right _ hb).1 h)]
      simp only [mul_assoc]
      rw [← mul_assoc F.c F.c, hF.c_sq, one_mul]
    · have hab : a * b ∈ F.del.ker := by
        rw [MonoidHom.mem_ker] at ha hb ⊢
        rw [map_mul, (Int.units_eq_one_or _).resolve_left ha, (Int.units_eq_one_or _).resolve_left hb]; simp
      rw [Subgroup.coe_mul, hcj, p2 _ ha, p2 _ hb, p1 _ hab]
      simp only [mul_assoc]
      rw [← mul_assoc F.c F.c, hF.c_sq, one_mul, mul_one]

end UpperTheory.V.Fr

/- English proof (translation)
Introduce `l _ k _ _ F C₀ hF`. Take `⟨t, ht⟩` from `ab_plus hF`. Take `⟨s', h, h0, hs', hm⟩` from `ab_minus hF`. Take `⟨π, hπ, hext⟩` from `ab_ext hF`. Use `haveI := hF.fin`.

Establish `hcop : (Nat.card kˣ).Coprime l` using `by haveI := Fintype.ofFinite k`. Take `⟨n, hl, hn⟩` from `FiniteField.card k l`. Rewrite using `[Nat.card_units, Nat.card_eq_fintype_card, hn]`. Use `Nat.Coprime.coprime_dvd_right (dvd_pow_self l n.ne_zero) ?_` and prove the remaining obligations. Conclude with `(Nat.coprime_self_sub_left (Nat.one_le_pow _ _ hl.pos)).2 (Nat.coprime_one_left _)`.

Establish `hcc : ∀ g, F.conj (F.conj g) = g` using `fun g => Subtype.ext (by show F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g`. Rewrite using `[inv_eq_of_mul_eq_one_right hF.c_sq]`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc F.c F.c, hF.c_sq, one_mul, mul_one])`. Establish `hcont : Continuous F.conj`.

Use `Continuous.subtype_mk (f := fun g : F.G0 => F.c * g * F.c⁻¹) (by fun_prop) _` and prove the remaining obligations. Use `⟨Fin.append (fun a => (π (t a) * F.conj (π (t a))) ^ Nat.card kˣ) s', s', h, h0, fun a => ?_, hs', fun A _ _ hA χ ho => ⟨fun hz => hm A hA χ ho ?_ fun a => by simpa using hz (Fin.natAdd _ a), hm A hA χ ho⟩⟩` and prove the remaining obligations. Use `Fin.addCases (fun a => ?_) (fun a => ?_) a` and prove the remaining obligations. Rewrite using `[Fin.append_left, Subgroup.coe_pow, map_pow, pow_card_eq_one']`. Rewrite using `[Fin.append_right]`.

Take `⟨v, g, -, h1, h2⟩` from `hs' a`. Rewrite using `[h2]`. Conclude with `h1`. Take `⟨φ, hφ⟩` from `hext A (χ * χ.comp F.conj) fun g => by simp [hcc, mul_comm]`. Establish `hop : IsOpen (φ.ker : Set F.Γ)`.

Use `Subgroup.isOpen_mono (H₁ := (χ.ker ⊓ χ.ker.comap F.conj).map F.del.ker.subtype) ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, ⟨h1, h2⟩, rfl⟩ show φ g = 1`. Rewrite using `[hφ, hπ]`. Conclude with `(congrArg₂ (· * ·) h1 h2).trans (mul_one 1)`. Conclude with `hF.del_open.isOpenMap_subtype_val _ (ho.inter (ho.preimage hcont))`.

Establish `h1` using `ht A hA φ hop fun a => by`. Use `hz (Fin.castAdd _ a)` as an intermediate fact. Rewrite `this` using `[Fin.append_left, map_pow, map_mul]`. Take `⟨n, hn⟩` from `hA (χ (π (t a)) * χ (F.conj (π (t a))))`. Rewrite using `[hφ]`.

Conclude with `orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcop.pow_right n) (orderOf_dvd_of_pow_eq_one this) (orderOf_dvd_of_pow_eq_one hn))`. Introduce `g`. Use `h1 (g⁻¹ : F.G0)` as an intermediate fact. Rewrite `this` using `[hφ, hπ]`. Establish `h2 : χ g⁻¹ * χ (F.star g) = 1` using `this`.

Rewrite `h2` using `[map_inv, inv_mul_eq_one]`. Conclude with `h2.symm`.
-/
theorem UpperTheory.V.Fr.ab_gen :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∃ (s : Fin (1 + C₀ + F.d) → F.G0) (s' : Fin F.d → F.G0) (h : ℕ), h ≠ 0 ∧ (∀ a, F.Ψ (s a) = 1) ∧ (∀ a, ∃ v g, g ∈ F.Iv v ∧ F.Ψ (F.loc v g) = 1 ∧ s' a = F.loc0 v g) ∧ ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.G0 →* A, IsOpen (χ.ker : Set F.G0) → ((∀ a, χ (s a) = 1) → ∀ g, χ g ^ h = 1) ∧ ((∀ g, χ (F.star g) = χ g) → (∀ a, χ (s' a) = 1) → ∀ g, χ g ^ h = 1) := by
  intro l _ k _ _ F C₀ hF
  obtain ⟨t, ht⟩ := ab_plus hF
  obtain ⟨s', h, h0, hs', hm⟩ := ab_minus hF
  obtain ⟨π, hπ, hext⟩ := ab_ext hF
  haveI := hF.fin
  have hcop : (Nat.card kˣ).Coprime l := by
    haveI := Fintype.ofFinite k
    obtain ⟨n, hl, hn⟩ := FiniteField.card k l
    rw [Nat.card_units, Nat.card_eq_fintype_card, hn]
    refine Nat.Coprime.coprime_dvd_right (dvd_pow_self l n.ne_zero) ?_
    exact (Nat.coprime_self_sub_left (Nat.one_le_pow _ _ hl.pos)).2 (Nat.coprime_one_left _)
  have hcc : ∀ g, F.conj (F.conj g) = g := fun g => Subtype.ext (by
    show F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g
    rw [inv_eq_of_mul_eq_one_right hF.c_sq]
    simp only [mul_assoc]
    rw [← mul_assoc F.c F.c, hF.c_sq, one_mul, mul_one])
  have hcont : Continuous F.conj := by
    refine Continuous.subtype_mk (f := fun g : F.G0 => F.c * g * F.c⁻¹) (by fun_prop) _
  refine ⟨Fin.append (fun a => (π (t a) * F.conj (π (t a))) ^ Nat.card kˣ) s', s', h, h0, fun a => ?_, hs',
    fun A _ _ hA χ ho => ⟨fun hz => hm A hA χ ho ?_ fun a => by simpa using hz (Fin.natAdd _ a), hm A hA χ ho⟩⟩
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · rw [Fin.append_left, Subgroup.coe_pow, map_pow, pow_card_eq_one']
    · rw [Fin.append_right]
      obtain ⟨v, g, -, h1, h2⟩ := hs' a
      rw [h2]; exact h1
  · obtain ⟨φ, hφ⟩ := hext A (χ * χ.comp F.conj) fun g => by simp [hcc, mul_comm]
    have hop : IsOpen (φ.ker : Set F.Γ) := by
      refine Subgroup.isOpen_mono (H₁ := (χ.ker ⊓ χ.ker.comap F.conj).map F.del.ker.subtype) ?_ ?_
      · rintro _ ⟨g, ⟨h1, h2⟩, rfl⟩
        show φ g = 1
        rw [hφ, hπ]
        exact (congrArg₂ (· * ·) h1 h2).trans (mul_one 1)
      · exact hF.del_open.isOpenMap_subtype_val _ (ho.inter (ho.preimage hcont))
    have h1 := ht A hA φ hop fun a => by
      have := hz (Fin.castAdd _ a)
      rw [Fin.append_left, map_pow, map_mul] at this
      obtain ⟨n, hn⟩ := hA (χ (π (t a)) * χ (F.conj (π (t a))))
      rw [hφ]
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcop.pow_right n) (orderOf_dvd_of_pow_eq_one this)
        (orderOf_dvd_of_pow_eq_one hn))
    intro g
    have := h1 (g⁻¹ : F.G0)
    rw [hφ, hπ] at this
    have h2 : χ g⁻¹ * χ (F.star g) = 1 := this
    rw [map_inv, inv_mul_eq_one] at h2
    exact h2.symm
