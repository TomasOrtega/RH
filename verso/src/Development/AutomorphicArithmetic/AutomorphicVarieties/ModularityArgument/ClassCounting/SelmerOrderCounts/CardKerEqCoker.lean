import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

section SlopeTestRemainingChoices

variable {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I)

/- English proof (translation)
Use `(injective_iff_map_eq_zero D.delI).2 fun z hz => ?_` and prove the remaining obligations. Establish `hg : D.gI z = D.a • z`. Simplify using `[Dat.delI, sub_eq_zero] at hz`. Conclude with `hz`. Establish `hk : ∀ k : ℕ, (D.gI ^ k) z = (D.a ^ k) • z`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, map_nsmul, hg, smul_smul, ← pow_succ]`.

Establish `h1` using `hk D.n`. Rewrite `h1` using `[D.gI_pow, Module.End.one_apply]`. Establish `ha : (2 : ℤ) ≤ D.a` using `by exact_mod_cast D.two_le`. Establish `hp : (2 : ℤ) ^ 1 ≤ (D.a : ℤ) ^ D.n` using `le_trans (pow_le_pow_right₀ (by norm_num) D.n_pos) (pow_le_pow_left₀ (by norm_num) ha _)`. Establish `hne : (D.a : ℤ) ^ D.n - 1 ≠ 0`.

Evaluate the numerical expressions using `at hp`. Use linear arithmetic over natural numbers and integers. Establish `hc : ((D.a : ℤ) ^ D.n) • z = (D.a ^ D.n) • z`. Rewrite using `[← Nat.cast_pow, natCast_zsmul]`. Use `D.tf _ z hne ?_` and prove the remaining obligations.

Rewrite using `[sub_smul, one_smul, hc, ← h1, sub_self]`.
-/
private theorem delI_inj : Function.Injective D.delI := by
  refine (injective_iff_map_eq_zero D.delI).2 fun z hz => ?_
  have hg : D.gI z = D.a • z := by
    simp [Dat.delI, sub_eq_zero] at hz
    exact hz
  have hk : ∀ k : ℕ, (D.gI ^ k) z = (D.a ^ k) • z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_nsmul, hg, smul_smul, ← pow_succ]
  have h1 := hk D.n
  rw [D.gI_pow, Module.End.one_apply] at h1
  have ha : (2 : ℤ) ≤ D.a := by exact_mod_cast D.two_le
  have hp : (2 : ℤ) ^ 1 ≤ (D.a : ℤ) ^ D.n :=
    le_trans (pow_le_pow_right₀ (by norm_num) D.n_pos) (pow_le_pow_left₀ (by norm_num) ha _)
  have hne : (D.a : ℤ) ^ D.n - 1 ≠ 0 := by
    norm_num at hp
    omega
  have hc : ((D.a : ℤ) ^ D.n) • z = (D.a ^ D.n) • z := by
    rw [← Nat.cast_pow, natCast_zsmul]
  refine D.tf _ z hne ?_
  rw [sub_smul, one_smul, hc, ← h1, sub_self]

/- English proof (translation)
Simplify using `[Dat.del, Dat.delI, D.comm]`.
-/
private theorem d_del (y : Y) : D.d (D.del y) = D.delI (D.d y) := by
  simp [Dat.del, Dat.delI, D.comm]

/- English proof (translation)
Take `⟨m, hm⟩` from `(Submodule.mem_torsion_iff t).1 ht`. Establish `hm' : (m : ℤ) • t = 0` using `hm`. Use `D.tf m _ (nonZeroDivisors.coe_ne_zero m) ?_` and prove the remaining obligations. Rewrite using `[← map_zsmul, hm', map_zero]`.
-/
private theorem d_tors {t : Y} (ht : t ∈ Submodule.torsion ℤ Y) : D.d t = 0 := by
  obtain ⟨m, hm⟩ := (Submodule.mem_torsion_iff t).1 ht
  have hm' : (m : ℤ) • t = 0 := hm
  refine D.tf m _ (nonZeroDivisors.coe_ne_zero m) ?_
  rw [← map_zsmul, hm', map_zero]

/- English proof (translation)
Establish `h1 : Nat.card C = Nat.card (C ⧸ LinearMap.ker f) * Nat.card (LinearMap.ker f)` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker f).toAddSubgroup`. Establish `h2 : Nat.card C = Nat.card (C ⧸ LinearMap.range f) * Nat.card (LinearMap.range f)` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.range f).toAddSubgroup`. Rewrite `h1` using `[Nat.card_congr f.quotKerEquivRange.toEquiv]`. Establish `hpos : 0 < Nat.card (LinearMap.range f)` using `Nat.card_pos`. Conclude with `Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans (h2.trans (mul_comm _ _)))`.
-/
private theorem card_ker_eq_coker {C : Type} [AddCommGroup C] [Finite C] (f : C →ₗ[ℤ] C) :
    Nat.card (LinearMap.ker f) = Nat.card (C ⧸ LinearMap.range f) := by
  have h1 : Nat.card C = Nat.card (C ⧸ LinearMap.ker f) * Nat.card (LinearMap.ker f) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker f).toAddSubgroup
  have h2 : Nat.card C = Nat.card (C ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.range f).toAddSubgroup
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv] at h1
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans (h2.trans (mul_comm _ _)))

/- English proof (translation)
Set `e` to `LinearEquiv.ofInjective D.delI (delI_inj D)`. Set `c : D.U →ₗ[ℤ] LinearMap.range D.delI` to `(D.d ∘ₗ D.U.subtype).codRestrict (LinearMap.range D.delI) (fun u => u.2)`. Use `⟨e.symm.toLinearMap ∘ₗ c, fun u => ?_⟩` and prove the remaining obligations. Establish `h` using `LinearEquiv.ofInjective_apply D.delI (h := delI_inj D) (e.symm (c u))`. Rewrite `h` using `[LinearEquiv.apply_symm_apply]`.

Conclude with `h.symm`.
-/
private theorem exists_psi : ∃ ψ : D.U →ₗ[ℤ] I, ∀ u : D.U, D.delI (ψ u) = D.d u := by
  let e := LinearEquiv.ofInjective D.delI (delI_inj D)
  let c : D.U →ₗ[ℤ] LinearMap.range D.delI :=
    (D.d ∘ₗ D.U.subtype).codRestrict (LinearMap.range D.delI) (fun u => u.2)
  refine ⟨e.symm.toLinearMap ∘ₗ c, fun u => ?_⟩
  have h := LinearEquiv.ofInjective_apply D.delI (h := delI_inj D) (e.symm (c u))
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `Y I _ _ D hC hE`. Take `⟨ψ, hψ⟩` from `exists_psi D`. Establish `hψ0 : ∀ u : D.U, D.d u = 0 → ψ u = 0` using `fun u hu => delI_inj D (by rw [hψ, hu, map_zero])`. Set `S` to `(LinearMap.range D.del ⊔ Submodule.torsion ℤ Y).submoduleOf D.U`. Set `p` to `LinearMap.range D.d`.

Establish `hpf : p ≤ p.comap D.delI`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `⟨D.del y, d_del D y⟩`. Set `f : (I ⧸ p) →ₗ[ℤ] (I ⧸ p)` to `p.mapQ p D.delI hpf`. Set `φ : D.U →ₗ[ℤ] I ⧸ p` to `p.mkQ ∘ₗ ψ`.

Establish `hSφ : S ≤ LinearMap.ker φ`. Introduce `u hu`. Express the relevant statement in the definitionally equal form `(u : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y at hu`. Take `⟨a, ⟨y, rfl⟩, t, ht, hat⟩` from `Submodule.mem_sup.1 hu`. Establish `hy : ψ u = D.d y` using `delI_inj D (by rw [hψ, ← hat, map_add, d_tors D ht, add_zero, d_del])`.

Express the relevant statement in the definitionally equal form `p.mkQ (ψ u) = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hy]`. Conclude with `LinearMap.mem_range_self _ _`. Set `φb : D.W →ₗ[ℤ] I ⧸ p` to `S.liftQ φ hSφ`. Establish `hkU : LinearMap.ker D.d ≤ D.U` using `fun y hy => by`.

Express the relevant statement in the definitionally equal form `D.d y ∈ LinearMap.range D.delI`. Rewrite using `[LinearMap.mem_ker.1 hy]`. Conclude with `zero_mem _`. Set `ι : LinearMap.ker D.d →ₗ[ℤ] D.W` to `S.mkQ ∘ₗ Submodule.inclusion hkU`. Establish `hrange : LinearMap.range φb = LinearMap.ker f` using `by show LinearMap.range (S.liftQ φ hSφ) = LinearMap.ker f`.

Rewrite using `[Submodule.range_liftQ]`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Rewrite using `[LinearMap.mem_ker]`.

Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (D.delI (ψ u)) : I ⧸ p) = 0`. Rewrite using `[hψ, Submodule.Quotient.mk_eq_zero]`. Conclude with `LinearMap.mem_range_self _ _`. Introduce `hx`. Take `⟨x, rfl⟩` from `Submodule.mkQ_surjective p x`.

Rewrite `hx` using `[LinearMap.mem_ker]`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (D.delI x) : I ⧸ p) = 0 at hx`. Rewrite `hx` using `[Submodule.Quotient.mk_eq_zero]`. Take `⟨y, hy⟩` from `hx`. Establish `hyU : y ∈ D.U` using `⟨x, hy.symm⟩`.

Establish `hψy : ψ ⟨y, hyU⟩ = x` using `delI_inj D (by rw [hψ]; exact hy)`. Use `⟨⟨y, hyU⟩, ?_⟩` and prove the remaining obligations. Use `show p.mkQ (ψ ⟨y, hyU⟩) = p.mkQ x`. Rewrite using `[hψy]`. Establish `hker : LinearMap.ker φb = LinearMap.range ι`.

Use extensionality with `w`. Take `⟨u, rfl⟩` from `Submodule.mkQ_surjective S w`. Prove the components needed by the constructor for the conclusion. Introduce `hu`. Rewrite `hu` using `[LinearMap.mem_ker]`.

Express the relevant statement in the definitionally equal form `p.mkQ (ψ u) = 0 at hu`. Rewrite `hu` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨y, hy⟩` from `hu`. Establish `hk : (u : Y) - D.del y ∈ LinearMap.ker D.d`. Rewrite using `[LinearMap.mem_ker, map_sub, d_del, hy, ← hψ, sub_self]`.

Use `⟨⟨_, hk⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `S.mkQ (Submodule.inclusion hkU ⟨_, hk⟩) = S.mkQ u`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Express the relevant statement in the definitionally equal form `((u : Y) - D.del y - u) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y`. Rewrite using `[sub_sub_cancel_left]`.

Conclude with `Submodule.mem_sup_left (Submodule.neg_mem _ (LinearMap.mem_range_self _ _))`. Introduce and unpack `⟨k, hk⟩`. Rewrite using `[LinearMap.mem_ker, ← hk]`. Establish `hk0 : ψ (Submodule.inclusion hkU k) = 0` using `hψ0 _ k.2`. Express the relevant statement in the definitionally equal form `p.mkQ (ψ (Submodule.inclusion hkU k)) = 0`.

Rewrite using `[hk0, map_zero]`. Establish `hkerι : LinearMap.ker ι = (Submodule.map D.del (LinearMap.ker D.d) ⊔ Submodule.torsion ℤ Y).submoduleOf (LinearMap.ker D.d)`. Use extensionality with `k`. Rewrite using `[LinearMap.mem_ker]`. Express the relevant statement in the definitionally equal form `S.mkQ (Submodule.inclusion hkU k) = 0 ↔ _`.

Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Express the relevant statement in the definitionally equal form `(k : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y ↔ (k : Y) ∈ Submodule.map D.del (LinearMap.ker D.d) ⊔ Submodule.torsion ℤ Y`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨a, ⟨y, rfl⟩, t, ht, hat⟩` from `Submodule.mem_sup.1 h`.

Establish `hy : D.d y = 0`. Apply `delI_inj D` to reduce the goal to its premises. Rewrite using `[map_zero, ← d_del]`. Establish `hk` using `k.2`. Rewrite `hk` using `[LinearMap.mem_ker, ← hat, map_add, d_tors D ht, add_zero]`.

Conclude with `hk`. Conclude with `Submodule.mem_sup.2 ⟨D.del y, ⟨y, hy, rfl⟩, t, ht, hat⟩`. Introduce `h`. Take `⟨a, ⟨y, -, rfl⟩, t, ht, hat⟩` from `Submodule.mem_sup.1 h`. Conclude with `Submodule.mem_sup.2 ⟨D.del y, LinearMap.mem_range_self _ _, t, ht, hat⟩`.

Use `haveI : Finite (I ⧸ p) := hC`. Use `haveI : Finite D.EQ := hE`. Establish `hr : LinearMap.range f = Submodule.map p.mkQ (LinearMap.range D.delI)`. Combine the equalities or inequalities in the displayed calculation. Establish `hQ : Finite ((I ⧸ p) ⧸ Submodule.map p.mkQ (LinearMap.range D.delI))` using `Finite.of_surjective _ (Submodule.mkQ_surjective _)`.

Establish `hClQ : Finite D.ClQ` using `Finite.of_equiv _ (Submodule.quotientQuotientEquivQuotientSup p (LinearMap.range D.delI)).toEquiv`. Establish `hcoker : Nat.card D.ClQ = Nat.card ((I ⧸ p) ⧸ LinearMap.range f)`. Rewrite using `[hr]`. Conclude with `Nat.card_congr (Submodule.quotientQuotientEquivQuotientSup p (LinearMap.range D.delI)).toEquiv.symm`. Establish `hkf` using `card_ker_eq_coker f`.

Establish `hEQ : Nat.card D.EQ = Nat.card (LinearMap.range ι)` using `Nat.card_congr ((Submodule.quotEquivOfEq _ _ hkerι.symm).trans ι.quotKerEquivRange).toEquiv`. Establish `hW : Nat.card D.W = Nat.card (D.W ⧸ LinearMap.ker φb) * Nat.card (LinearMap.ker φb)` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker φb).toAddSubgroup`. Establish `hmain : Nat.card D.W = Nat.card D.EQ * Nat.card D.ClQ`. Rewrite using `[hW, Nat.card_congr φb.quotKerEquivRange.toEquiv, hrange, hkf, ← hcoker, hker, ← hEQ]`. Conclude with `mul_comm _ _`.

Establish `hne : Nat.card D.W ≠ 0`. Rewrite using `[hmain]`. Conclude with `Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'`. Conclude with `⟨hClQ, Nat.finite_of_card_ne_zero hne, hmain⟩`.
-/
theorem UpperTheory.V.ZK.Ct.cardW :
    ∀ (Y I : Type) [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I), Finite (I ⧸ LinearMap.range D.d) → Finite D.EQ → Finite D.ClQ ∧ Finite D.W ∧ Nat.card D.W = Nat.card D.EQ * Nat.card D.ClQ := by
  intro Y I _ _ D hC hE
  obtain ⟨ψ, hψ⟩ := exists_psi D
  have hψ0 : ∀ u : D.U, D.d u = 0 → ψ u = 0 := fun u hu =>
    delI_inj D (by rw [hψ, hu, map_zero])
  let S := (LinearMap.range D.del ⊔ Submodule.torsion ℤ Y).submoduleOf D.U
  let p := LinearMap.range D.d
  have hpf : p ≤ p.comap D.delI := by
    rintro _ ⟨y, rfl⟩
    exact ⟨D.del y, d_del D y⟩
  let f : (I ⧸ p) →ₗ[ℤ] (I ⧸ p) := p.mapQ p D.delI hpf
  let φ : D.U →ₗ[ℤ] I ⧸ p := p.mkQ ∘ₗ ψ
  have hSφ : S ≤ LinearMap.ker φ := by
    intro u hu
    change (u : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y at hu
    obtain ⟨a, ⟨y, rfl⟩, t, ht, hat⟩ := Submodule.mem_sup.1 hu
    have hy : ψ u = D.d y :=
      delI_inj D (by rw [hψ, ← hat, map_add, d_tors D ht, add_zero, d_del])
    change p.mkQ (ψ u) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hy]
    exact LinearMap.mem_range_self _ _
  let φb : D.W →ₗ[ℤ] I ⧸ p := S.liftQ φ hSφ
  have hkU : LinearMap.ker D.d ≤ D.U := fun y hy => by
    change D.d y ∈ LinearMap.range D.delI
    rw [LinearMap.mem_ker.1 hy]
    exact zero_mem _
  let ι : LinearMap.ker D.d →ₗ[ℤ] D.W := S.mkQ ∘ₗ Submodule.inclusion hkU
  have hrange : LinearMap.range φb = LinearMap.ker f := by
    show LinearMap.range (S.liftQ φ hSφ) = LinearMap.ker f
    rw [Submodule.range_liftQ]
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      rw [LinearMap.mem_ker]
      change (Submodule.Quotient.mk (D.delI (ψ u)) : I ⧸ p) = 0
      rw [hψ, Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self _ _
    · intro hx
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective p x
      rw [LinearMap.mem_ker] at hx
      change (Submodule.Quotient.mk (D.delI x) : I ⧸ p) = 0 at hx
      rw [Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨y, hy⟩ := hx
      have hyU : y ∈ D.U := ⟨x, hy.symm⟩
      have hψy : ψ ⟨y, hyU⟩ = x := delI_inj D (by rw [hψ]; exact hy)
      refine ⟨⟨y, hyU⟩, ?_⟩
      show p.mkQ (ψ ⟨y, hyU⟩) = p.mkQ x
      rw [hψy]
  have hker : LinearMap.ker φb = LinearMap.range ι := by
    ext w
    obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective S w
    constructor
    · intro hu
      rw [LinearMap.mem_ker] at hu
      change p.mkQ (ψ u) = 0 at hu
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu
      obtain ⟨y, hy⟩ := hu
      have hk : (u : Y) - D.del y ∈ LinearMap.ker D.d := by
        rw [LinearMap.mem_ker, map_sub, d_del, hy, ← hψ, sub_self]
      refine ⟨⟨_, hk⟩, ?_⟩
      change S.mkQ (Submodule.inclusion hkU ⟨_, hk⟩) = S.mkQ u
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      change ((u : Y) - D.del y - u) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y
      rw [sub_sub_cancel_left]
      exact Submodule.mem_sup_left (Submodule.neg_mem _ (LinearMap.mem_range_self _ _))
    · rintro ⟨k, hk⟩
      rw [LinearMap.mem_ker, ← hk]
      have hk0 : ψ (Submodule.inclusion hkU k) = 0 := hψ0 _ k.2
      change p.mkQ (ψ (Submodule.inclusion hkU k)) = 0
      rw [hk0, map_zero]
  have hkerι : LinearMap.ker ι = (Submodule.map D.del (LinearMap.ker D.d) ⊔
      Submodule.torsion ℤ Y).submoduleOf (LinearMap.ker D.d) := by
    ext k
    rw [LinearMap.mem_ker]
    change S.mkQ (Submodule.inclusion hkU k) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (k : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y ↔
      (k : Y) ∈ Submodule.map D.del (LinearMap.ker D.d) ⊔ Submodule.torsion ℤ Y
    constructor
    · intro h
      obtain ⟨a, ⟨y, rfl⟩, t, ht, hat⟩ := Submodule.mem_sup.1 h
      have hy : D.d y = 0 := by
        apply delI_inj D
        rw [map_zero, ← d_del]
        have hk := k.2
        rw [LinearMap.mem_ker, ← hat, map_add, d_tors D ht, add_zero] at hk
        exact hk
      exact Submodule.mem_sup.2 ⟨D.del y, ⟨y, hy, rfl⟩, t, ht, hat⟩
    · intro h
      obtain ⟨a, ⟨y, -, rfl⟩, t, ht, hat⟩ := Submodule.mem_sup.1 h
      exact Submodule.mem_sup.2 ⟨D.del y, LinearMap.mem_range_self _ _, t, ht, hat⟩
  haveI : Finite (I ⧸ p) := hC
  haveI : Finite D.EQ := hE
  have hr : LinearMap.range f = Submodule.map p.mkQ (LinearMap.range D.delI) :=
    calc LinearMap.range f = LinearMap.range (f ∘ₗ p.mkQ) :=
          (LinearMap.range_comp_of_range_eq_top f (Submodule.range_mkQ p)).symm
      _ = LinearMap.range (p.mkQ ∘ₗ D.delI) := by rw [Submodule.mapQ_mkQ]
      _ = Submodule.map p.mkQ (LinearMap.range D.delI) := LinearMap.range_comp _ _
  have hQ : Finite ((I ⧸ p) ⧸ Submodule.map p.mkQ (LinearMap.range D.delI)) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hClQ : Finite D.ClQ :=
    Finite.of_equiv _ (Submodule.quotientQuotientEquivQuotientSup p (LinearMap.range D.delI)).toEquiv
  have hcoker : Nat.card D.ClQ = Nat.card ((I ⧸ p) ⧸ LinearMap.range f) := by
    rw [hr]
    exact Nat.card_congr (Submodule.quotientQuotientEquivQuotientSup p (LinearMap.range D.delI)).toEquiv.symm
  have hkf := card_ker_eq_coker f
  have hEQ : Nat.card D.EQ = Nat.card (LinearMap.range ι) :=
    Nat.card_congr ((Submodule.quotEquivOfEq _ _ hkerι.symm).trans ι.quotKerEquivRange).toEquiv
  have hW : Nat.card D.W = Nat.card (D.W ⧸ LinearMap.ker φb) * Nat.card (LinearMap.ker φb) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker φb).toAddSubgroup
  have hmain : Nat.card D.W = Nat.card D.EQ * Nat.card D.ClQ := by
    rw [hW, Nat.card_congr φb.quotKerEquivRange.toEquiv, hrange, hkf, ← hcoker, hker, ← hEQ]
    exact mul_comm _ _
  have hne : Nat.card D.W ≠ 0 := by
    rw [hmain]
    exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  exact ⟨hClQ, Nat.finite_of_card_ne_zero hne, hmain⟩
