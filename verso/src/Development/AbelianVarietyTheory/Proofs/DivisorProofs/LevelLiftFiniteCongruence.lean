import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelEqHalfMarkingStabilizer
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftCong

/- English proof (translation)
Introduce `z hz`. Use `choose t htS ht using hy`. Use `set x : Fin n → B := (Units.val (β⁻¹ : GL (Fin n) B)).mulVec (fun a => s (z a)) with hx`. Establish `hxS : ∀ i, x i ∈ S` using `(hL z).1 hz`. Take `⟨w, hw⟩ : ∃ w : Fin n → A, (fun a => s (w a)) = β.val.mulVec ((Matrix.of t).mulVec x)` from `by choose f hf using hs.2`.

Conclude with `⟨fun a => f _, funext fun a => hf _⟩`. Use `⟨w, (hL w).2 fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hw, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] show ∑ j, t i j * x j ∈ S`. Conclude with `S.sum_mem fun j _ => S.mul_mem (htS i j) (hxS j)`. Establish `hz' : (fun a => s (z a)) = β.val.mulVec x`.

Rewrite using `[hx, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Establish `hm : s c • (y.map S.subtype - 1) = (N : B) • Matrix.of t`. Use extensionality with `i j`. Use `ht i j` as an intermediate fact. Simplify using `only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, smul_eq_mul, Matrix.of_apply, Subring.coe_subtype]`.

Rewrite using `[← this]`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`. Establish `e1 : (k.map s).mulVec (s c • fun a => s (z a)) - (s c • fun a => s (z a)) = (N : B) • fun a => s (w a)`. Rewrite using `[hw, hk, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, ← hx, hz', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul _ (N : B), ← Matrix.smul_mulVec (N : B), ← hm, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mulVec_sub, smul_sub]`. Use function extensionality and compare the values at `i`.

Apply `hs.1` to reduce the goal to its premises. Establish `e2` using `congrFun e1 i`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply] at e2`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, map_sub, map_sum, map_mul, nsmul_eq_mul, map_natCast]`. Conclude with `e2`.
-/
theorem move_mem_of_entries {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (s : A →+* B)
    (hs : Function.Bijective s) (S : Subring B) (β : GL (Fin n) B) (L : AddSubgroup (Fin n → A))
    (hL : ∀ z, z ∈ L ↔ ∀ i, (Units.val (β⁻¹ : GL (Fin n) B)).mulVec (fun a => s (z a)) i ∈ S)
    (k : Matrix (Fin n) (Fin n) A) (y : Matrix (Fin n) (Fin n) S)
    (hk : k.map s = β.val * y.map S.subtype * (β⁻¹ : GL (Fin n) B).val) (c : A) (N : ℕ)
    (hy : ∀ i j, ∃ t ∈ S, s c * (((y - 1 : Matrix (Fin n) (Fin n) S) i j : S) : B) = N * t) :
    ∀ z ∈ L, ∃ w ∈ L, k.mulVec (fun i => c * z i) - (fun i => c * z i) = N • w := by
  classical
  intro z hz
  choose t htS ht using hy
  set x : Fin n → B := (Units.val (β⁻¹ : GL (Fin n) B)).mulVec (fun a => s (z a)) with hx
  have hxS : ∀ i, x i ∈ S := (hL z).1 hz
  obtain ⟨w, hw⟩ : ∃ w : Fin n → A, (fun a => s (w a)) = β.val.mulVec ((Matrix.of t).mulVec x) := by
    choose f hf using hs.2
    exact ⟨fun a => f _, funext fun a => hf _⟩
  refine ⟨w, (hL w).2 fun i => ?_, ?_⟩
  · rw [hw, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    show ∑ j, t i j * x j ∈ S
    exact S.sum_mem fun j _ => S.mul_mem (htS i j) (hxS j)
  · have hz' : (fun a => s (z a)) = β.val.mulVec x := by
      rw [hx, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have hm : s c • (y.map S.subtype - 1) = (N : B) • Matrix.of t := by
      ext i j
      have := ht i j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, smul_eq_mul, Matrix.of_apply,
        Subring.coe_subtype]
      rw [← this]
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    have e1 : (k.map s).mulVec (s c • fun a => s (z a)) - (s c • fun a => s (z a)) =
        (N : B) • fun a => s (w a) := by
      rw [hw, hk, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, ← hx, hz', ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_smul _ (N : B), ← Matrix.smul_mulVec (N : B), ← hm, Matrix.smul_mulVec, Matrix.sub_mulVec,
        Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mulVec_sub, smul_sub]
    funext i
    apply hs.1
    have e2 := congrFun e1 i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply] at e2
    simp only [Pi.sub_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, map_sub, map_sum, map_mul, nsmul_eq_mul,
      map_natCast]
    exact e2

/- English proof (translation)
Take `⟨q, hq⟩` from `Formalism.L2.DIV.cmpS_surj (F := F) I h0 (Ideal.Quotient.mk _ s)`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Establish `hd : Formalism.L2.DIV.oToS F E a - s ∈ Formalism.L2.DIV.idS F I` using `Ideal.Quotient.eq.1 hq`. Establish `ha : a ∈ I`. Apply `hI` to reduce the goal to its premises.

Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`. Introduce and unpack `J ⟨hJ, hp⟩`. Set `w : Formalism.L2.DIV.Pl E` to `⟨J, hp, fun h => h0 (le_bot_iff.1 (h ▸ hJ))⟩`. Establish `h1 : Formalism.L2.DIV.resS F w (Formalism.L2.DIV.oToS F E a - s) = 0`. Establish `: Formalism.L2.DIV.idS F I ≤ RingHom.ker (Formalism.L2.DIV.resS F w)`.

Use `Ideal.map_le_iff_le_comap.2 fun b hb => ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, Formalism.L2.DIV.resS_oToS]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hJ hb)`. Conclude with `this hd`. Rewrite `h1` using `[map_sub, hs w hJ, sub_zero, Formalism.L2.DIV.resS_oToS]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h1`. Use `sub_mem (Ideal.mem_map_of_mem (Formalism.L2.DIV.oToS F E) ha) hd` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem mem_idS_of_resS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (I : Ideal (𝓞 E)) (h0 : I ≠ ⊥) (hI : I.IsRadical) (s : Formalism.L2.Herm.intAf F E)
    (hs : ∀ w : Formalism.L2.DIV.Pl E, I ≤ w.asIdeal → Formalism.L2.DIV.resS F w s = 0) : s ∈ Formalism.L2.DIV.idS F I := by
  obtain ⟨q, hq⟩ := Formalism.L2.DIV.cmpS_surj (F := F) I h0 (Ideal.Quotient.mk _ s)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hd : Formalism.L2.DIV.oToS F E a - s ∈ Formalism.L2.DIV.idS F I := Ideal.Quotient.eq.1 hq
  have ha : a ∈ I := by
    apply hI
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hp⟩
    let w : Formalism.L2.DIV.Pl E := ⟨J, hp, fun h => h0 (le_bot_iff.1 (h ▸ hJ))⟩
    have h1 : Formalism.L2.DIV.resS F w (Formalism.L2.DIV.oToS F E a - s) = 0 := by
      have : Formalism.L2.DIV.idS F I ≤ RingHom.ker (Formalism.L2.DIV.resS F w) := by
        refine Ideal.map_le_iff_le_comap.2 fun b hb => ?_
        rw [Ideal.mem_comap, RingHom.mem_ker, Formalism.L2.DIV.resS_oToS]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (hJ hb)
      exact this hd
    rw [map_sub, hs w hJ, sub_zero, Formalism.L2.DIV.resS_oToS] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  have := sub_mem (Ideal.mem_map_of_mem (Formalism.L2.DIV.oToS F E) ha) hd
  rwa [sub_sub_cancel] at this

/- English proof (translation)
Establish `h4` using `congrArg S.subtype h`. Rewrite `h4` using `[map_mul, map_mul, map_natCast]`. Rewrite using `[mul_comm, mul_comm (N : B)]`. Conclude with `h4.symm`.
-/
theorem coe_mul_eq_of_eq {B : Type} [CommRing B] (S : Subring B) (t e c : S) (N : ℕ) (h : t * N = e * c) :
    (c : B) * (e : B) = N * (t : B) := by
  have h4 := congrArg S.subtype h
  rw [map_mul, map_mul, map_natCast] at h4
  rw [mul_comm, mul_comm (N : B)]
  exact h4.symm

/- English proof (translation)
The claim follows from `(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective`.
-/
theorem swapAE_bijective (D : D7) : Function.Bijective (swapAE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Establish `h1` using `congrArg Units.val (Formalism.L2.DIV.frGL_pullFr β ⟨finR V rfl κ, h⟩)`. Conclude with `h1.symm`.
-/
theorem finHom_map_eq {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (κ : GA D V)
    (h : finR V rfl κ ∈ Formalism.L2.DIV.St β) :
    (finHom V κ).1.map (swapAE D) =
      β.val * (Formalism.L2.DIV.pullFr β ⟨finR V rfl κ, h⟩).val.map (OAf D).subtype * (β⁻¹ : GL (Fin V.rank) (EAf D)).val := by
  have h1 := congrArg Units.val (Formalism.L2.DIV.frGL_pullFr β ⟨finR V rfl κ, h⟩)
  exact h1.symm

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D H l V r hr β Pg hβ hPg`. Substitute `hr` using the available equality. Use `⟨fun g κ hκ z hz => ?_, fun hrad κ hκ => ?_⟩` and prove the remaining obligations. Take `⟨-, h, -⟩` from `hκ`. Use `move_mem_of_entries (swapAE D) (swapAE_bijective D) (OAf D) β (latHat V) hβ _ _ (finHom_map_eq V β κ h) 1 1 (fun i j => ⟨_, SetLike.coe_mem ((_ - 1 : Matrix _ _ (OAf D)) i j), by rw [map_one, Nat.cast_one]⟩) z hz` as an intermediate fact.

Simplify using `only [one_mul] at this`. Conclude with `this`. Take `⟨-, h, hw⟩` from `hκ`. Rewrite using `[GlobalTheory.Member.finCong_iff_half D H l V κ]`. Introduce `b hb`.

Use `move_mem_of_entries (swapAE D) (swapAE_bijective D) (OAf D) β (latHat V) hβ _ _ (finHom_map_eq V β κ h) ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) l.M (fun i j => ?_)` and prove the remaining obligations. Establish `h0 : l.Mb ≠ ⊥`. Introduce `h0`. Establish `hp` using `l.prod`. Rewrite `hp` using `[h0, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot]`.

Establish `h3` using `l.three_le`. Establish `: l.M = 0` using `by exact_mod_cast hp`. Use linear arithmetic over natural numbers and integers. Generalize the expression as in `hy : Formalism.L2.DIV.pullFr β ⟨finR V rfl κ, h⟩ = y`. Establish `he : (y.val - 1) i j ∈ Formalism.L2.DIV.idS D.host.F l.Mb`.

Use `mem_idS_of_resS _ h0 hrad _ fun w hle => ?_` and prove the remaining obligations. Establish `h1 : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F w) y = 1`. Rewrite using `[← hy]`. Conclude with `hw ⟨w, (hPg w).2 hle⟩`. Establish `h2 : Formalism.L2.DIV.resS D.host.F w (y.val i j) = (1 : Matrix _ _ (Formalism.L2.DIV.kP w)) i j` using `congrArg (fun g : GL (Fin V.rank) (Formalism.L2.DIV.kP w) => g.val i j) h1`.

Rewrite using `[Matrix.sub_apply, map_sub, h2]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Establish `hm : (y.val - 1) i j * Formalism.L2.DIV.oToS D.host.F D.host.E b ∈ Ideal.span {((l.M : ℕ) : OAf D)}`. Use `Ideal.mul_mem_mul he (Ideal.mem_map_of_mem (Formalism.L2.DIV.oToS D.host.F D.host.E) hb)` as an intermediate fact. Rewrite `this` using `[Formalism.L2.DIV.idS, ← Ideal.map_mul, l.prod, Ideal.map_span, Set.image_singleton, map_natCast]`.

Conclude with `this`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 hm`. Use `⟨t, t.2, ?_⟩` and prove the remaining obligations. Conclude with `coe_mul_eq_of_eq _ _ _ _ _ ht`.
-/
theorem lift_finCong : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsLatBasis V hr β → (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → (∀ (g : Formalism.L2.DIV.G0 Pg r) κ, IsLift V hr β Pg g κ → FinCong V 1 κ) ∧ (l.Mb.IsRadical → ∀ κ, IsLift V hr β Pg 1 κ → FinCong V l.M κ) := by
  intro D H l V r hr β Pg hβ hPg
  subst hr
  refine ⟨fun g κ hκ z hz => ?_, fun hrad κ hκ => ?_⟩
  · obtain ⟨-, h, -⟩ := hκ
    have := move_mem_of_entries (swapAE D) (swapAE_bijective D) (OAf D) β (latHat V) hβ _ _
      (finHom_map_eq V β κ h) 1 1 (fun i j => ⟨_, SetLike.coe_mem ((_ - 1 : Matrix _ _ (OAf D)) i j), by rw [map_one, Nat.cast_one]⟩) z hz
    simp only [one_mul] at this
    exact this
  · obtain ⟨-, h, hw⟩ := hκ
    rw [GlobalTheory.Member.finCong_iff_half D H l V κ]
    intro b hb
    refine move_mem_of_entries (swapAE D) (swapAE_bijective D) (OAf D) β (latHat V) hβ _ _
      (finHom_map_eq V β κ h) ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) l.M (fun i j => ?_)
    have h0 : l.Mb ≠ ⊥ := by
      intro h0
      have hp := l.prod
      rw [h0, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hp
      have h3 := l.three_le
      have : l.M = 0 := by exact_mod_cast hp
      omega
    generalize hy : Formalism.L2.DIV.pullFr β ⟨finR V rfl κ, h⟩ = y
    have he : (y.val - 1) i j ∈ Formalism.L2.DIV.idS D.host.F l.Mb := by
      refine mem_idS_of_resS _ h0 hrad _ fun w hle => ?_
      have h1 : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F w) y = 1 := by
        rw [← hy]; exact hw ⟨w, (hPg w).2 hle⟩
      have h2 : Formalism.L2.DIV.resS D.host.F w (y.val i j) = (1 : Matrix _ _ (Formalism.L2.DIV.kP w)) i j :=
        congrArg (fun g : GL (Fin V.rank) (Formalism.L2.DIV.kP w) => g.val i j) h1
      rw [Matrix.sub_apply, map_sub, h2]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have hm : (y.val - 1) i j * Formalism.L2.DIV.oToS D.host.F D.host.E b ∈
        Ideal.span {((l.M : ℕ) : OAf D)} := by
      have := Ideal.mul_mem_mul he (Ideal.mem_map_of_mem (Formalism.L2.DIV.oToS D.host.F D.host.E) hb)
      rw [Formalism.L2.DIV.idS, ← Ideal.map_mul, l.prod, Ideal.map_span, Set.image_singleton, map_natCast] at this
      exact this
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨t, t.2, ?_⟩
    exact coe_mul_eq_of_eq _ _ _ _ _ ht

end GlobalTheory.LiftCong
