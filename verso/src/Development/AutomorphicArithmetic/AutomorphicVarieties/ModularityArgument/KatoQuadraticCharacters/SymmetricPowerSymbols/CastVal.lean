import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Apply `ε.injective` to reduce the goal to its premises. Rewrite using `[map_pow, eps_eOm, eps_eOm, ← Complex.exp_nat_mul]`. Use `congr 1`. Establish `h1 : (k : ℂ) ≠ 0` using `by exact_mod_cast hk.ne'`.

Establish `h2 : (m : ℂ) ≠ 0` using `by exact_mod_cast hm.ne'`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
private theorem eOm_red (ε : Ω →+* ℂ) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    eOm ε (1 / ((k * m : ℕ) : ℚ)) ^ k = eOm ε (1 / (m : ℚ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  apply ε.injective
  rw [map_pow, eps_eOm, eps_eOm, ← Complex.exp_nat_mul]
  congr 1
  have h1 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have h2 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

/- English proof (translation)
Unfold `zt`. Rewrite using `[← map_pow, ← map_pow, eOm_red ε hk hm]`.
-/
private theorem zt_red (X : Tower Ω ε) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) : zt X (k * m) ^ k = zt X m := by
  unfold zt
  rw [← map_pow, ← map_pow, eOm_red ε hk hm]

/- English proof (translation)
Use `haveI : NeZero (k * m) := ⟨(Nat.mul_pos hk hm).ne'⟩`. Rewrite using `[ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]`.
-/
private theorem cast_val {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (i : ZMod (k * m)) :
    (ZMod.castHom (dvd_mul_left m k) (ZMod m) i).val = i.val % m := by
  haveI : NeZero (k * m) := ⟨(Nat.mul_pos hk hm).ne'⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

/- English proof (translation)
Take `⟨-, hrep1, -, -, -, -, -⟩` from `lgB Ω ε X (k * m) (Nat.mul_pos hk hm)`. Take `⟨hp2, -, huniq2, -, -, -, -⟩` from `lgB Ω ε X m hm`. Apply `huniq2 _ _ _ (pow_ne_zero _ hb)` to reduce the goal to its premises. Rewrite using `[cast_val hk hm]`. Establish `e : zt X m ^ (lg X (k * m) a b).val = zt X m ^ ((lg X (k * m) a b).val % m)` using `by conv_lhs => rw [← Nat.div_add_mod (lg X (k * m) a b).val m, pow_add, pow_mul, hp2.pow_eq_one, one_pow, one_mul]`.

Rewrite using `[← e, ← zt_red X hk hm, ← pow_mul, mul_comm k (lg X (k * m) a b).val, pow_mul, ← mul_pow, ← hrep1 a b hb h]`.
-/
private theorem lg_red (X : Tower Ω ε) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) {a b : Kb X} (hb : b ≠ 0)
    (h : a ^ (k * m) = b ^ (k * m)) :
    lg X m (a ^ k) (b ^ k) = ZMod.castHom (dvd_mul_left m k) (ZMod m) (lg X (k * m) a b) := by
  obtain ⟨-, hrep1, -, -, -, -, -⟩ := lgB Ω ε X (k * m) (Nat.mul_pos hk hm)
  obtain ⟨hp2, -, huniq2, -, -, -, -⟩ := lgB Ω ε X m hm
  apply huniq2 _ _ _ (pow_ne_zero _ hb)
  rw [cast_val hk hm]
  have e : zt X m ^ (lg X (k * m) a b).val = zt X m ^ ((lg X (k * m) a b).val % m) := by
    conv_lhs => rw [← Nat.div_add_mod (lg X (k * m) a b).val m, pow_add, pow_mul, hp2.pow_eq_one,
      one_pow, one_mul]
  rw [← e, ← zt_red X hk hm, ← pow_mul, mul_comm k (lg X (k * m) a b).val, pow_mul, ← mul_pow,
    ← hrep1 a b hb h]

/- English proof (translation)
Establish `h0 : θ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hθ` using `[zero_pow (Nat.mul_pos hk hm).ne']`. Conclude with `hu ((map_eq_zero _).1 hθ.symm)`. Unfold `ka`.

Rewrite using `[map_pow]`. Conclude with `lg_red X hk hm h0 (by rw [← map_pow, hθ, hh])`.
-/
private theorem ka_red (X : Tower Ω ε) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) {θ : Kb X} {u : X.K} (hu : u ≠ 0)
    (hθ : θ ^ (k * m) = io X u) {h : RingAut (Kb X)} (hh : InD X h) :
    ka X m (θ ^ k) h = ZMod.castHom (dvd_mul_left m k) (ZMod m) (ka X (k * m) θ h) := by
  have h0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.mul_pos hk hm).ne'] at hθ
    exact hu ((map_eq_zero _).1 hθ.symm)
  unfold ka
  rw [map_pow]
  exact lg_red X hk hm h0 (by rw [← map_pow, hθ, hh])

/- English proof (translation)
Use `haveI : NeZero m := ⟨hm.ne'⟩`. Take `⟨hp, -, -, -, -, -, hcyc⟩` from `lgB Ω ε X m hm`. Take `⟨-, -, -, -, -, -, hcyc2⟩` from `lgB Ω ε X (k * m) (Nat.mul_pos hk hm)`. Establish `hζ : IsPrimitiveRoot (eOm ε (1 / (m : ℚ))) m` using `IsPrimitiveRoot.of_map_of_injective (f := (io X).comp (algebraMap Ω X.K)) hp (RingHom.injective _)`. Establish `h1 : (eOm ε (1 / (m : ℚ))) ^ m = 1` using `hζ.pow_eq_one`.

Establish `hA` using `(hcyc s s).2.2 _ h1`. Establish `hB` using `(hcyc2 s s).2.2 _ (by rw [mul_comm, pow_mul, h1, one_pow])`. Apply `ZMod.val_injective` to reduce the goal to its premises. Apply `hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)` to reduce the goal to its premises. Rewrite using `[← hA, cast_val hk hm, hB]`.

Use `conv_lhs => rw [← Nat.div_add_mod (cyc (k * m) s).val m, pow_add, pow_mul, h1, one_pow, one_mul]`.
-/
private theorem cyc_red (X : Tower Ω ε) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (s : Ω ≃ₐ[ℚ] Ω) :
    cyc m s = ZMod.castHom (dvd_mul_left m k) (ZMod m) (cyc (k * m) s) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨hp, -, -, -, -, -, hcyc⟩ := lgB Ω ε X m hm
  obtain ⟨-, -, -, -, -, -, hcyc2⟩ := lgB Ω ε X (k * m) (Nat.mul_pos hk hm)
  have hζ : IsPrimitiveRoot (eOm ε (1 / (m : ℚ))) m :=
    IsPrimitiveRoot.of_map_of_injective (f := (io X).comp (algebraMap Ω X.K)) hp
      (RingHom.injective _)
  have h1 : (eOm ε (1 / (m : ℚ))) ^ m = 1 := hζ.pow_eq_one
  have hA := (hcyc s s).2.2 _ h1
  have hB := (hcyc2 s s).2.2 _ (by rw [mul_comm, pow_mul, h1, one_pow])
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← hA, cast_val hk hm, hB]
  conv_lhs => rw [← Nat.div_add_mod (cyc (k * m) s).val m, pow_add, pow_mul, h1, one_pow, one_mul]

end

/- English proof (translation)
Introduce `Ω _ _ _ ε X k m hk hm`. Establish `hkm` using `Nat.mul_pos hk hm`. Use `⟨fun u v P hP => ⟨hP.hu, hP.hv, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hP.ha, pow_mul]`. Both sides reduce to the same expression.

Rewrite using `[← hP.hb, pow_mul]`. Both sides reduce to the same expression. Introduce `g h hg hh`. Simplify using `only [Pt.red]`. Rewrite using `[ka_red X hk hm hP.hu.1 hP.ha hg, ka_red X hk hm hP.hv.1 hP.hb hh, ← map_mul, hP.cob g h hg hh, map_add, map_sub]`.

Take `⟨B, hB⟩` from `hP.lc`. Use `⟨B, fun h h' a b c => ?_⟩` and prove the remaining obligations. Simplify using `only [Pt.red]`. Rewrite using `[hB h h' a b c]`. Introduce `B h a b c`.

Simplify using `only [Pt.red]`. Rewrite using `[hP.unr B h a b c, map_zero]`. Introduce and unpack `τ s - u v P Q hP hQ f ⟨σ, hσ, θ, hθ, hd⟩`. Use `⟨σ, hσ, θ ^ k, by rw [← hθ, pow_mul], fun h hh => ?_⟩` and prove the remaining obligations. Establish `nz : ∀ (a : Kb X) (w : X.K), w ≠ 0 → a ^ (k * m) = io X w → a ≠ 0`.

Introduce and unpack `a w hw ha rfl`. Rewrite `ha` using `[zero_pow hkm.ne']`. Conclude with `hw ((map_eq_zero _).1 ha.symm)`. Establish `ea : σ P.a ^ (k * m) = Q.a ^ (k * m)` using `by rw [← map_pow, hP.ha, hσ, hQ.ha]`. Establish `eb : σ P.b ^ (k * m) = Q.b ^ (k * m)` using `by rw [← map_pow, hP.hb, hσ, hQ.hb]`.

Rewrite using `[ka_red X hk hm f.ne_zero hθ hh, hd h hh]`. Simplify using `only [dif, Pt.mv, Pt.red, map_add, map_sub, map_mul, map_pow]`. Rewrite using `[ka_red X hk hm hQ.hu.1 hQ.ha hh, ka_red X hk hm hQ.hv.1 hQ.hb hh, lg_red X hk hm (nz _ _ hQ.hu.1 hQ.ha) ea, lg_red X hk hm (nz _ _ hQ.hv.1 hQ.hb) eb, cyc_red X hk hm s]`.
-/
theorem UpperTheory.V.Z.Kato.Sym.redB :
    UpperTheory.V.Z.Kato.Sym.RedB := by
  intro Ω _ _ _ ε X k m hk hm
  have hkm := Nat.mul_pos hk hm
  refine ⟨fun u v P hP => ⟨hP.hu, hP.hv, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← hP.ha, pow_mul]; rfl
  · rw [← hP.hb, pow_mul]; rfl
  · intro g h hg hh
    simp only [Pt.red]
    rw [ka_red X hk hm hP.hu.1 hP.ha hg, ka_red X hk hm hP.hv.1 hP.hb hh, ← map_mul, hP.cob g h hg hh, map_add, map_sub]
  · obtain ⟨B, hB⟩ := hP.lc
    refine ⟨B, fun h h' a b c => ?_⟩
    simp only [Pt.red]
    rw [hB h h' a b c]
  · intro B h a b c
    simp only [Pt.red]
    rw [hP.unr B h a b c, map_zero]
  · rintro τ s - u v P Q hP hQ f ⟨σ, hσ, θ, hθ, hd⟩
    refine ⟨σ, hσ, θ ^ k, by rw [← hθ, pow_mul], fun h hh => ?_⟩
    have nz : ∀ (a : Kb X) (w : X.K), w ≠ 0 → a ^ (k * m) = io X w → a ≠ 0 := by
      rintro a w hw ha rfl
      rw [zero_pow hkm.ne'] at ha
      exact hw ((map_eq_zero _).1 ha.symm)
    have ea : σ P.a ^ (k * m) = Q.a ^ (k * m) := by rw [← map_pow, hP.ha, hσ, hQ.ha]
    have eb : σ P.b ^ (k * m) = Q.b ^ (k * m) := by rw [← map_pow, hP.hb, hσ, hQ.hb]
    rw [ka_red X hk hm f.ne_zero hθ hh, hd h hh]
    simp only [dif, Pt.mv, Pt.red, map_add, map_sub, map_mul, map_pow]
    rw [ka_red X hk hm hQ.hu.1 hQ.ha hh, ka_red X hk hm hQ.hv.1 hQ.hb hh, lg_red X hk hm (nz _ _ hQ.hu.1 hQ.ha) ea,
      lg_red X hk hm (nz _ _ hQ.hv.1 hQ.hb) eb, cyc_red X hk hm s]
