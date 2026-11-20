import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal

noncomputable section

namespace GlobalTheory.LvT.ValEq

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

section Local

variable {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ}

/- English proof (translation)
Simplify using `only [LocF.std, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]`. Use `forall_congr' fun a => ⟨?_, fun h => ⟨⟨x a, h⟩, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem mem_std (x : Fin n → Lc.K) : x ∈ Lc.std n ↔ ∀ a, x a ∈ Lc.O := by
  simp only [LocF.std, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  refine forall_congr' fun a => ⟨?_, fun h => ⟨⟨x a, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]; exact y.2

/- English proof (translation)
Establish `h1 : (Pi.single b 1 : Fin n → Lc.K) ∈ Lc.std n`. Rewrite using `[mem_std]`. Introduce `c`. Distinguish the cases in `h : c = b`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`. Use `(mem_std _).1 (hk _ h1) a` as an intermediate fact. Simplify using `using this`.
-/
theorem entry_mem (k : Matrix (Fin n) (Fin n) Lc.K) (hk : ∀ x ∈ Lc.std n, k.mulVec x ∈ Lc.std n) (a b : Fin n) :
    k a b ∈ Lc.O := by
  have h1 : (Pi.single b 1 : Fin n → Lc.K) ∈ Lc.std n := by
    rw [mem_std]; intro c
    by_cases h : c = b
    · subst h; simp
    · simp [h]
  have := (mem_std _).1 (hk _ h1) a
  simpa using this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `p.2.smul 0 0 p.1.L.zero_mem` as an intermediate fact. Simplify using `using this`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, p.2.add _ (p.1.L.smul_mem _ (he a)) _ (p.1.L.sum_mem fun b _ => p.1.L.smul_mem _ (he b)), ih, p.2.smul _ _ (he a)]`.
-/
theorem f_sum (p : LocF.PP Lc n) (s : Finset (Fin n)) (c : Fin n → Lc.O) (e : Fin n → Fin n → Lc.K)
    (he : ∀ b, e b ∈ p.1.L) : p.1.f (∑ b ∈ s, c b • e b) = ∑ b ∈ s, Lc.res (c b) * p.1.f (e b) := by
  induction s using Finset.induction_on with
  | empty =>
    have := p.2.smul 0 0 p.1.L.zero_mem
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      p.2.add _ (p.1.L.smul_mem _ (he a)) _ (p.1.L.sum_mem fun b _ => p.1.L.smul_mem _ (he b)), ih,
      p.2.smul _ _ (he a)]

/- English proof (translation)
Take `⟨h, hh⟩` from `p.2.lat`. Use `set e : Fin n → Fin n → Lc.K := fun b => Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (Pi.single b 1) with he`. Establish `heL : ∀ b, e b ∈ p.1.L` using `fun b => (hh _).2 (by`. Rewrite using `[mem_std]`. Introduce `c`.

Distinguish the cases in `h : c = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h])`. Establish `hf : ∀ y : Fin n → Lc.O, p.1.f (Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (fun b => (y b : Lc.K))) = ∑ b, Lc.res (y b) * p.1.f (e b)`.

Introduce `y`. Rewrite using `[← f_sum p _ y e heL]`. Use `congr 1`. Use extensionality with `a`. Simplify using `[he, Matrix.mulVec, dotProduct, Finset.sum_apply, Subring.smul_def, mul_comm]`.

Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, p.1.f (e a) ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨x, hx⟩` from `p.2.ne`. Establish `hxL : x ∈ p.1.L`.

Assume the negation of the conclusion as `h'`. Conclude with `hx (p.2.off x h')`. Use `set y := Matrix.mulVec ((h⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x with hy`. Establish `hxy : Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) y = x`. Rewrite using `[hy, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`.

Establish `hyS` using `(mem_std _).1 ((hh y).1 (hxy ▸ hxL))`. Use `hf fun b => ⟨y b, hyS b⟩` as an intermediate fact. Apply `hx` to reduce the goal to its premises. Rewrite using `[← hxy]`. Simplify `this` using `[hne]`.

Use `choose c0 hc0 using fun b => Lc.res_surj (p.1.f (e b) / p.1.f (e a))`. Set `c : Fin n → Lc.O` to `Function.update c0 a 1`. Establish `hca : c a = 1` using `by simp [c]`. Establish `hc : ∀ b, Lc.res (c b) * p.1.f (e a) = p.1.f (e b)`. Introduce `b`.

Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Simplify using `[hca]`. Simplify using `only [c, Function.update_of_ne hb, hc0]`. Clear the denominators using the available nonvanishing facts.

Set `m : Matrix (Fin n) (Fin n) Lc.K` to `Matrix.updateRow 1 a fun b => ((q : Lc.K))⁻¹ * (c b : Lc.K)`. Establish `hma : ∀ y, m.mulVec y a = ((q : Lc.K))⁻¹ * ∑ b, (c b : Lc.K) * y b`. Introduce `y`. Simplify using `[m, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Establish `hmb : ∀ y b, b ≠ a → m.mulVec y b = y b`.

Introduce `y b hb`. Simplify using `[m, Matrix.mulVec, Matrix.updateRow_ne hb, dotProduct, Matrix.one_apply]`. Establish `hsplit : ∀ y : Fin n → Lc.K, ∑ b, (c b : Lc.K) * y b = y a + ∑ b ∈ Finset.univ.erase a, (c b : Lc.K) * y b`. Introduce `y`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ a), hca]`.

Simplify using the standard rewrite rules. Establish `hq` using `Lc.q_ne`. Establish `hu : IsUnit m`. Rewrite using `[← Matrix.mulVec_injective_iff_isUnit]`. Introduce `y y' hyy`.

Establish `hb : ∀ b, b ≠ a → y b = y' b` using `fun b hb => by rw [← hmb y b hb, ← hmb y' b hb, hyy]`. Establish `h1` using `congrFun hyy a`. Rewrite `h1` using `[hma, hma, hsplit, hsplit]`. Establish `h2` using `mul_left_cancel₀ (inv_ne_zero hq) h1`. Rewrite `h2` using `[Finset.sum_congr rfl fun b hb' => by rw [hb b (Finset.ne_of_mem_erase hb')]]`.

Use function extensionality and compare the values at `b`. Distinguish the cases in `hba : b = a`. Substitute `hba` using the available equality. Conclude with `add_right_cancel h2`. Conclude with `hb b hba`.

Establish `key : ∀ y, Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) y ∈ p.ker ↔ m.mulVec y ∈ Lc.std n`. Introduce `y`. Establish `hres : ∀ hy : ∀ b, y b ∈ Lc.O, p.1.f (Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) y) = 0 ↔ ∃ t : Lc.O, ∑ b, (c b : Lc.K) * y b = (q : Lc.K) * t`. Introduce `hy`. Establish `h1` using `hf fun b => ⟨y b, hy b⟩`.

Establish `h2` using `Lc.res_ker (∑ b, c b * ⟨y b, hy b⟩)`. Establish `h3 : ∑ b, Lc.res ⟨y b, hy b⟩ * p.1.f (e b) = Lc.res (∑ b, c b * ⟨y b, hy b⟩) * p.1.f (e a)`. Rewrite using `[map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← hc b, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h4 : ((∑ b, c b * ⟨y b, hy b⟩ : Lc.O) : Lc.K) = ∑ b, (c b : Lc.K) * y b` using `by push_cast; rfl`. Rewrite `h2` using `[h4]`. Rewrite using `[← h2]`. Express the relevant statement in the definitionally equal form `p.1.f (Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) y) = _ at h1`.

Rewrite using `[h1, h3, mul_eq_zero, or_iff_left ha]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Establish `hy` using `(mem_std _).1 ((hh y).1 h1)`. Take `⟨t, ht⟩` from `(hres hy).1 h2`.

Rewrite using `[mem_std]`. Introduce `b`. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Rewrite using `[hma, ht, inv_mul_cancel_left₀ hq]`.

Conclude with `t.2`. Rewrite using `[hmb _ _ hb]`. Conclude with `hy b`. Introduce `h1`. Rewrite `h1` using `[mem_std]`.

Establish `ht : ∑ b, (c b : Lc.K) * y b = (q : Lc.K) * (⟨_, h1 a⟩ : Lc.O)`. Simplify using `only [hma]`. Rewrite using `[mul_inv_cancel_left₀ hq]`. Establish `hy : ∀ b, y b ∈ Lc.O`. Introduce `b`.

Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Establish `: y b = (q : Lc.K) * m.mulVec y b - ∑ b' ∈ Finset.univ.erase b, (c b' : Lc.K) * y b'`. Rewrite using `[eq_sub_iff_add_eq, ← hsplit, ht]`. Rewrite using `[this]`.

Use `Lc.O.sub_mem (Lc.O.mul_mem (natCast_mem _ _) (h1 b)) (Lc.O.sum_mem fun b' hb' => Lc.O.mul_mem (c b').2 ?_)` and prove the remaining obligations. Rewrite using `[← hmb y b' (Finset.ne_of_mem_erase hb')]`. Conclude with `h1 b'`. Rewrite using `[← hmb y b hb]`. Conclude with `h1 b`.

Conclude with `⟨(hh y).2 ((mem_std _).2 hy), (hres hy).2 ⟨_, ht⟩⟩`. Take `⟨mu, hmu⟩` from `hu`. Use `⟨h * mu⁻¹, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec, key, Matrix.mulVec_mulVec, ← hmu, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`.
-/
theorem exists_frame_ker (p : LocF.PP Lc n) :
    ∃ h : GL (Fin n) Lc.K, ∀ x, Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) x ∈ p.ker ↔ x ∈ Lc.std n := by
  obtain ⟨h, hh⟩ := p.2.lat
  set e : Fin n → Fin n → Lc.K := fun b => Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (Pi.single b 1) with he
  have heL : ∀ b, e b ∈ p.1.L := fun b => (hh _).2 (by
    rw [mem_std]; intro c
    by_cases h : c = b
    · subst h; simp
    · simp [h])
  have hf : ∀ y : Fin n → Lc.O, p.1.f (Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (fun b => (y b : Lc.K))) =
      ∑ b, Lc.res (y b) * p.1.f (e b) := by
    intro y
    rw [← f_sum p _ y e heL]
    congr 1
    ext a
    simp [he, Matrix.mulVec, dotProduct, Finset.sum_apply, Subring.smul_def, mul_comm]
  obtain ⟨a, ha⟩ : ∃ a, p.1.f (e a) ≠ 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨x, hx⟩ := p.2.ne
    have hxL : x ∈ p.1.L := by
      by_contra h'; exact hx (p.2.off x h')
    set y := Matrix.mulVec ((h⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x with hy
    have hxy : Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) y = x := by
      rw [hy, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hyS := (mem_std _).1 ((hh y).1 (hxy ▸ hxL))
    have := hf fun b => ⟨y b, hyS b⟩
    apply hx
    rw [← hxy]
    simpa [hne] using this
  choose c0 hc0 using fun b => Lc.res_surj (p.1.f (e b) / p.1.f (e a))
  let c : Fin n → Lc.O := Function.update c0 a 1
  have hca : c a = 1 := by simp [c]
  have hc : ∀ b, Lc.res (c b) * p.1.f (e a) = p.1.f (e b) := by
    intro b
    by_cases hb : b = a
    · subst hb; simp [hca]
    · simp only [c, Function.update_of_ne hb, hc0]; field_simp
  let m : Matrix (Fin n) (Fin n) Lc.K := Matrix.updateRow 1 a fun b => ((q : Lc.K))⁻¹ * (c b : Lc.K)
  have hma : ∀ y, m.mulVec y a = ((q : Lc.K))⁻¹ * ∑ b, (c b : Lc.K) * y b := by
    intro y
    simp [m, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hmb : ∀ y b, b ≠ a → m.mulVec y b = y b := by
    intro y b hb
    simp [m, Matrix.mulVec, Matrix.updateRow_ne hb, dotProduct, Matrix.one_apply]
  have hsplit : ∀ y : Fin n → Lc.K, ∑ b, (c b : Lc.K) * y b = y a + ∑ b ∈ Finset.univ.erase a, (c b : Lc.K) * y b := by
    intro y
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), hca]; simp
  have hq := Lc.q_ne
  have hu : IsUnit m := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro y y' hyy
    have hb : ∀ b, b ≠ a → y b = y' b := fun b hb => by rw [← hmb y b hb, ← hmb y' b hb, hyy]
    have h1 := congrFun hyy a
    rw [hma, hma, hsplit, hsplit] at h1
    have h2 := mul_left_cancel₀ (inv_ne_zero hq) h1
    rw [Finset.sum_congr rfl fun b hb' => by rw [hb b (Finset.ne_of_mem_erase hb')]] at h2
    funext b
    by_cases hba : b = a
    · subst hba; exact add_right_cancel h2
    · exact hb b hba
  have key : ∀ y, Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) y ∈ p.ker ↔ m.mulVec y ∈ Lc.std n := by
    intro y
    have hres : ∀ hy : ∀ b, y b ∈ Lc.O, p.1.f (Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) y) = 0 ↔
        ∃ t : Lc.O, ∑ b, (c b : Lc.K) * y b = (q : Lc.K) * t := by
      intro hy
      have h1 := hf fun b => ⟨y b, hy b⟩
      have h2 := Lc.res_ker (∑ b, c b * ⟨y b, hy b⟩)
      have h3 : ∑ b, Lc.res ⟨y b, hy b⟩ * p.1.f (e b) = Lc.res (∑ b, c b * ⟨y b, hy b⟩) * p.1.f (e a) := by
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← hc b, map_mul]; ring
      have h4 : ((∑ b, c b * ⟨y b, hy b⟩ : Lc.O) : Lc.K) = ∑ b, (c b : Lc.K) * y b := by
        push_cast; rfl
      rw [h4] at h2
      rw [← h2]
      change p.1.f (Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) y) = _ at h1
      rw [h1, h3, mul_eq_zero, or_iff_left ha]
    constructor
    · rintro ⟨h1, h2⟩
      have hy := (mem_std _).1 ((hh y).1 h1)
      obtain ⟨t, ht⟩ := (hres hy).1 h2
      rw [mem_std]
      intro b
      by_cases hb : b = a
      · subst hb
        rw [hma, ht, inv_mul_cancel_left₀ hq]; exact t.2
      · rw [hmb _ _ hb]; exact hy b
    · intro h1
      rw [mem_std] at h1
      have ht : ∑ b, (c b : Lc.K) * y b = (q : Lc.K) * (⟨_, h1 a⟩ : Lc.O) := by
        simp only [hma]; rw [mul_inv_cancel_left₀ hq]
      have hy : ∀ b, y b ∈ Lc.O := by
        intro b
        by_cases hb : b = a
        · subst hb
          have : y b = (q : Lc.K) * m.mulVec y b - ∑ b' ∈ Finset.univ.erase b, (c b' : Lc.K) * y b' := by
            rw [eq_sub_iff_add_eq, ← hsplit, ht]
          rw [this]
          refine Lc.O.sub_mem (Lc.O.mul_mem (natCast_mem _ _) (h1 b)) (Lc.O.sum_mem fun b' hb' => Lc.O.mul_mem (c b').2 ?_)
          rw [← hmb y b' (Finset.ne_of_mem_erase hb')]; exact h1 b'
        · rw [← hmb y b hb]; exact h1 b
      exact ⟨(hh y).2 ((mem_std _).2 hy), (hres hy).2 ⟨_, ht⟩⟩
  obtain ⟨mu, hmu⟩ := hu
  refine ⟨h * mu⁻¹, fun x => ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, key, Matrix.mulVec_mulVec, ← hmu, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.one_mulVec]

end Local

section Coeff

open Formalism.UG.P

/- English proof (translation)
Unfold `roundAct Formalism.UG.dwAct`. Rewrite using `[wlocal_map_smul, wlocal_map_rowAct, ← map_inv]`. Use `congr 1`. Unfold `detPow`. Establish `: Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ g) = Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g)`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `[RingHom.map_det]`. Rewrite using `[this, ← map_zpow (Units.map φ.toMonoidHom)]`. Both sides reduce to the same expression.
-/
theorem map_roundAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (l : DomWeight n) (g : GL (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) :
    MvPolynomial.map φ (roundAct R n l g f) =
      roundAct S n l (Matrix.GeneralLinearGroup.map φ g) (MvPolynomial.map φ f) := by
  unfold roundAct Formalism.UG.dwAct
  rw [wlocal_map_smul, wlocal_map_rowAct, ← map_inv]
  congr 1
  unfold detPow
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ g) =
      Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
    apply Units.ext
    simp [RingHom.map_det]
  rw [this, ← map_zpow (Units.map φ.toMonoidHom)]
  rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Both sides reduce to the same expression.
-/
theorem invTr_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (g : GL (Fin n) R) :
    inside₂ S n (Matrix.GeneralLinearGroup.map φ g) = Matrix.GeneralLinearGroup.map φ (inside₂ R n g) := by
  apply Units.ext
  rfl

/- English proof (translation)
Rewrite using `[bridge_round_square_holds]`. Conclude with `(factSqStable R n l _).2 f hf`.
-/
theorem roundAct_mem {R : Type} [CommRing R] {n : ℕ} (l : DomWeight n) (g : GL (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : f ∈ delSq R n l) : roundAct R n l g f ∈ delSq R n l := by
  rw [bridge_round_square_holds]
  exact (factSqStable R n l _).2 f hf

def roundL {n : ℕ} (l : DomWeight n) (g : GL (Fin n) ℂ) :
    MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  detPow ℂ n g (-l.detShift) • (Formalism.UG.dwAct ℂ n n g).toLinearMap

/- English proof (translation)
The claim follows from `Formalism.MainNotions.product_first_zeroth_parts.blk_ten (fun τ => roundL (l τ) (g τ)) f`.
-/
theorem blk_round_ten {ι : Type} [Fintype ι] {n : ℕ} (l : ι → DomWeight n) (g : ι → GL (Fin n) ℂ)
    (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    blk (fun τ => roundAct ℂ n (l τ) (g τ)) (ten f) = ten fun τ => roundAct ℂ n (l τ) (g τ) (f τ) :=
  Formalism.MainNotions.product_first_zeroth_parts.blk_ten (fun τ => roundL (l τ) (g τ)) f

/- English proof (translation)
The claim follows from `Module.Basis.constr_basis _ _ _ _`.
-/
theorem blk_basis {ι : Type} [Fintype ι] {n : ℕ}
    (F : ι → MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ) (mon : ι × Fin n × Fin n →₀ ℕ) :
    blk F (MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ mon) = ten fun τ => F τ (MvPolynomial.monomial
      (mon.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) 1) :=
  Module.Basis.constr_basis _ _ _ _

/- English proof (translation)
Establish `: blk (fun τ => roundAct ℂ n (l τ) (g τ * k τ)) = blk (fun τ => roundAct ℂ n (l τ) (g τ)) ∘ₗ blk (fun τ => roundAct ℂ n (l τ) (k τ))`. Apply `(MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).ext` to reduce the goal to its premises. Introduce `mon`. Rewrite using `[LinearMap.comp_apply, blk_basis, blk_basis, blk_round_ten]`. Conclude with `congrArg ten (funext fun τ => (factSqActMul ℂ n (l τ) _ _ _).2)`.

Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem blk_round_mul {ι : Type} [Fintype ι] {n : ℕ} (l : ι → DomWeight n) (g k : ι → GL (Fin n) ℂ)
    (z : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    blk (fun τ => roundAct ℂ n (l τ) (g τ * k τ)) z =
      blk (fun τ => roundAct ℂ n (l τ) (g τ)) (blk (fun τ => roundAct ℂ n (l τ) (k τ)) z) := by
  have : blk (fun τ => roundAct ℂ n (l τ) (g τ * k τ)) =
      blk (fun τ => roundAct ℂ n (l τ) (g τ)) ∘ₗ blk (fun τ => roundAct ℂ n (l τ) (k τ)) := by
    apply (MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).ext
    intro mon
    rw [LinearMap.comp_apply, blk_basis, blk_basis, blk_round_ten]
    exact congrArg ten (funext fun τ => (factSqActMul ℂ n (l τ) _ _ _).2)
  rw [this]; rfl

variable {D : D7}

def embO (D : D7) (w : D.what₂.places.Pl) : Ow D w →+* ℂ := D.what₂.embLL.comp (Ow D w).subtype

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨s, f, hs, hf, rfl⟩` from `hx`. Use `AddSubgroup.subset_closure ⟨r * s, f, (Ow D w).mul_mem hr hs, hf, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, map_mul]`.

Consider the case `zero => rw [smul_zero]`. Conclude with `AddSubgroup.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `AddSubgroup.add_mem _ hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`.

Conclude with `AddSubgroup.neg_mem _ hx`.
-/
theorem smul_mem_intSpan {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ Ow D w) (z : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) (hz : z ∈ IntSpan D w lam) :
    D.what₂.embLL r • z ∈ IntSpan D w lam := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨s, f, hs, hf, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨r * s, f, (Ow D w).mul_mem hr hs, hf, ?_⟩
    rw [smul_smul, map_mul]
  | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

/- English proof (translation)
Use `choose c hc using fun τ => Finsupp.mem_span_range_iff_exists_finsupp.1 (hf τ)`. Establish `h1 : (fun τ => MvPolynomial.map (embO D w) (f τ)) = fun τ => ∑ a ∈ (c τ).support, embO D w (c τ a) • MvPolynomial.map (Int.castRingHom ℂ) (Formalism.GradedWeylDivisibility.applyWord ℤ a (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW))`. Use function extensionality and compare the values at `τ`. Rewrite using `[← hc τ, Finsupp.sum, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[wlocal_map_smul, wlocal_map_applyWord, wlocal_map_applyWord, wlocal_map_hw, wlocal_map_hw]`. Rewrite using `[h1, ← Formalism.MainNotions.product_first_zeroth_parts.tenM_apply, MultilinearMap.map_sum_finset]`. Use `AddSubgroup.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.map_smul_univ, Formalism.MainNotions.product_first_zeroth_parts.tenM_apply, ← map_prod]`. Conclude with `AddSubgroup.subset_closure ⟨_, fun τ => Formalism.GradedWeylDivisibility.applyWord ℤ (a τ) (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW), (∏ τ, c τ (a τ)).2, fun τ => Submodule.subset_span ⟨a τ, rfl⟩, rfl⟩`.
-/
theorem ten_mem_intSpan {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n)
    (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) (Ow D w)) (hf : ∀ τ, f τ ∈ delSq (Ow D w) n (lam τ)) :
    ten (fun τ => MvPolynomial.map (embO D w) (f τ)) ∈ IntSpan D w lam := by
  choose c hc using fun τ => Finsupp.mem_span_range_iff_exists_finsupp.1 (hf τ)
  have h1 : (fun τ => MvPolynomial.map (embO D w) (f τ)) = fun τ => ∑ a ∈ (c τ).support,
      embO D w (c τ a) • MvPolynomial.map (Int.castRingHom ℂ)
        (Formalism.GradedWeylDivisibility.applyWord ℤ a (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW)) := by
    funext τ
    rw [← hc τ, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [wlocal_map_smul, wlocal_map_applyWord, wlocal_map_applyWord, wlocal_map_hw, wlocal_map_hw]
  rw [h1, ← Formalism.MainNotions.product_first_zeroth_parts.tenM_apply, MultilinearMap.map_sum_finset]
  refine AddSubgroup.sum_mem _ fun a _ => ?_
  rw [MultilinearMap.map_smul_univ, Formalism.MainNotions.product_first_zeroth_parts.tenM_apply, ← map_prod]
  exact AddSubgroup.subset_closure ⟨_, fun τ => Formalism.GradedWeylDivisibility.applyWord ℤ (a τ) (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW),
    (∏ τ, c τ (a τ)).2, fun τ => Submodule.subset_span ⟨a τ, rfl⟩, rfl⟩

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨r, f, hr, hf, rfl⟩` from `hx`. Rewrite using `[map_smul, blk_round_ten]`. Use `smul_mem_intSpan w lam r hr _ ?_` and prove the remaining obligations.

Use `ten_mem_intSpan w lam (fun τ => roundAct (Ow D w) n (wSh (lam τ) s) (g τ) (MvPolynomial.map (Int.castRingHom _) (f τ))) (fun τ => by` as an intermediate fact. Rewrite using `[← Formalism.MainNotions.product_first_zeroth_parts.delSq_wSh _ (lam τ) s]`. Apply `roundAct_mem` to reduce the goal to its premises. Rewrite using `[Formalism.MainNotions.product_first_zeroth_parts.delSq_wSh]`. Conclude with `wlocal_map_weyl _ _ _ _ (hf τ))`.

Use `this using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `τ`. Rewrite using `[map_roundAct, MvPolynomial.map_map, RingHom.ext_int ((embO D w).comp (Int.castRingHom _)) (Int.castRingHom ℂ)]`. Consider the case `zero => rw [map_zero]`. Conclude with `AddSubgroup.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `AddSubgroup.add_mem _ hx hy`. Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `AddSubgroup.neg_mem _ hx`.
-/
theorem blk_mem_intSpan {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (s : ℤ)
    (g : D.what₂.Tau → GL (Fin n) (Ow D w))
    (z : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) (hz : z ∈ IntSpan D w lam) :
    blk (fun τ => roundAct ℂ n (wSh (lam τ) s) (Matrix.GeneralLinearGroup.map (embO D w) (g τ))) z ∈
      IntSpan D w lam := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hr, hf, rfl⟩ := hx
    rw [map_smul, blk_round_ten]
    refine smul_mem_intSpan w lam r hr _ ?_
    have := ten_mem_intSpan w lam
      (fun τ => roundAct (Ow D w) n (wSh (lam τ) s) (g τ) (MvPolynomial.map (Int.castRingHom _) (f τ))) (fun τ => by
        rw [← Formalism.MainNotions.product_first_zeroth_parts.delSq_wSh _ (lam τ) s]
        apply roundAct_mem
        rw [Formalism.MainNotions.product_first_zeroth_parts.delSq_wSh]
        exact wlocal_map_weyl _ _ _ _ (hf τ))
    convert this using 2
    funext τ
    rw [map_roundAct, MvPolynomial.map_map, RingHom.ext_int ((embO D w).comp (Int.castRingHom _)) (Int.castRingHom ℂ)]
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact AddSubgroup.neg_mem _ hx

/- English proof (translation)
Establish `key : ∀ (m m' : Matrix (Fin n) (Fin n) K) (hm : ∀ a b, j (m a b) ∈ A) (hm' : ∀ a b, j (m' a b) ∈ A), m * m' = 1 → (Matrix.of fun a b => (⟨_, hm a b⟩ : A)) * (Matrix.of fun a b => (⟨_, hm' a b⟩ : A)) = 1`. Introduce `m m' hm hm' h`. Use extensionality with `a b`. Use `congrArg j (congrFun (congrFun h a) b)` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, map_sum]`.

Rewrite using `[Matrix.mul_apply]`. Apply the tactic sequence `by_cases hab : a = b <;> simpa [Matrix.one_apply, hab] using this`. Conclude with `⟨⟨_, _, key _ _ h1 h2 (Units.mul_inv k), key _ _ h2 h1 (Units.inv_mul k)⟩, fun _ _ => rfl⟩`.
-/
theorem exists_lift {K L : Type} [Field K] [Field L] (A : Subring L) (j : K →+* L) {n : ℕ} (k : GL (Fin n) K)
    (h1 : ∀ a b, j ((k : Matrix (Fin n) (Fin n) K) a b) ∈ A)
    (h2 : ∀ a b, j (((k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b) ∈ A) :
    ∃ g : GL (Fin n) A, ∀ a b, ((g : Matrix (Fin n) (Fin n) A) a b : L) = j ((k : Matrix (Fin n) (Fin n) K) a b) := by
  have key : ∀ (m m' : Matrix (Fin n) (Fin n) K) (hm : ∀ a b, j (m a b) ∈ A) (hm' : ∀ a b, j (m' a b) ∈ A),
      m * m' = 1 → (Matrix.of fun a b => (⟨_, hm a b⟩ : A)) * (Matrix.of fun a b => (⟨_, hm' a b⟩ : A)) = 1 := by
    intro m m' hm hm' h
    ext a b
    have := congrArg j (congrFun (congrFun h a) b)
    rw [Matrix.mul_apply, map_sum] at this
    rw [Matrix.mul_apply]
    by_cases hab : a = b <;> simpa [Matrix.one_apply, hab] using this
  exact ⟨⟨_, _, key _ _ h1 h2 (Units.mul_inv k), key _ _ h2 h1 (Units.inv_mul k)⟩, fun _ _ => rfl⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(0 : WithTop ℤ) ≤ D.what₂.places.val w ζ`. Establish `h1` using `congrArg (D.what₂.places.val w) h`. Rewrite `h1` using `[AddValuation.map_pow, AddValuation.map_one]`. Proceed by induction on `hv : D.what₂.places.val w ζ using WithTop.recTopCoe with`. Consider the case `top => exact le_top`.

Consider the case `coe a`. Rewrite `h1` using `[hv, ← WithTop.coe_nsmul, ← WithTop.coe_zero, WithTop.coe_inj, nsmul_eq_mul, mul_eq_zero]`. Break down `h1 with h1 | h1` into its components or cases. Conclude with `absurd h1 (by exact_mod_cast hk.ne')`. Rewrite using `[h1]`.

Conclude with `le_rfl`.
-/
theorem mem_Ow_of_pow (w : D.what₂.places.Pl) (ζ : D.what₂.LL) (k : ℕ) (hk : 0 < k) (h : ζ ^ k = 1) : ζ ∈ Ow D w := by
  change (0 : WithTop ℤ) ≤ D.what₂.places.val w ζ
  have h1 := congrArg (D.what₂.places.val w) h
  rw [AddValuation.map_pow, AddValuation.map_one] at h1
  induction hv : D.what₂.places.val w ζ using WithTop.recTopCoe with
  | top => exact le_top
  | coe a =>
    rw [hv, ← WithTop.coe_nsmul, ← WithTop.coe_zero, WithTop.coe_inj, nsmul_eq_mul, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (by exact_mod_cast hk.ne')
    · rw [h1]; exact le_rfl

end Coeff

section Main

variable {D : D7} {u : D.what₂.Word} {X : Ch D u} {i : ℕ} {M : PtModel X i} (Co : M.Coord)

/- English proof (translation)
Unfold `PtModel.Coord.mov`. Rewrite using `[← blk_round_mul]`. Establish `: ∀ τ, Co.mv w (fun v => h v * k v) τ = Co.mv w h τ * Co.mv w k τ`. Introduce `τ`. Unfold `PtModel.Coord.mv`.

Simplify using `only`. Use `split_ifs`. Rewrite using `[map_mul]`. Rewrite using `[map_mul, invTr_mul]`. Simplify using `only [this]`.
-/
theorem mov_mul (w : D.what₂.places.Pl) (h k : ∀ v, GL (Fin (D.R.N i)) (M.Lc v).K)
    (z : MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ) :
    Co.mov w (fun v => h v * k v) z = Co.mov w h (Co.mov w k z) := by
  unfold PtModel.Coord.mov
  rw [← blk_round_mul]
  have : ∀ τ, Co.mv w (fun v => h v * k v) τ = Co.mv w h τ * Co.mv w k τ := by
    intro τ
    unfold PtModel.Coord.mv
    dsimp only
    split_ifs
    · rw [map_mul]
    · rw [map_mul, invTr_mul]
  simp only [this]

/- English proof (translation)
Establish `hl : ∀ v, ∃ g : GL (Fin (D.R.N i)) (Ow D w), Matrix.GeneralLinearGroup.map (embO D w) g = Matrix.GeneralLinearGroup.map (D.what₂.embLL.comp (Co.j w v)) (k v)`. Introduce `v`. Take `⟨g, hg⟩` from `exists_lift (Ow D w) (Co.j w v) (k v) (fun a b => (Co.j_int w hw v _).2 (entry_mem _ (fun x hx => (hk v x).2 hx) a b)) (fun a b => (Co.j_int w hw v _).2 (entry_mem _ (fun x hx => (hk v _).1 (by`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec])) a b))` and apply the resulting hypothesis. Use `⟨g, Units.ext (Matrix.ext fun a b => ?_)⟩` and prove the remaining obligations.

Conclude with `congrArg D.what₂.embLL (hg a b)`. Use `choose g hg using hl`. Use `blk_mem_intSpan w (X.fm.lam i) ((i * (D.R.t + 1) / 2 : ℕ) : ℤ) (fun τ => if X.fm.seenP w then g ((X.fm.tauOf w).symm τ) else inside₂ _ _ (g ((X.fm.tauOf w).symm τ))) z hz` as an intermediate fact. Establish `e : ∀ τ, Co.mv w k τ = Matrix.GeneralLinearGroup.map (embO D w) (if X.fm.seenP w then g ((X.fm.tauOf w).symm τ) else inside₂ _ _ (g ((X.fm.tauOf w).symm τ)))`. Introduce `τ`.

Unfold `PtModel.Coord.mv`. Simplify using `only`. Use `split_ifs`. Rewrite using `[hg]`. Rewrite using `[← invTr_map, hg]`.

Unfold `PtModel.Coord.mov PtModel.lamT`. Simplify using `only [e]`. Conclude with `this`.
-/
theorem mov_mem (w : D.what₂.places.Pl) (hw : OverT X w) (k : ∀ v, GL (Fin (D.R.N i)) (M.Lc v).K)
    (hk : ∀ v x, Matrix.mulVec (k v : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (M.Lc v).K) x ∈ (M.Lc v).std (D.R.N i) ↔
      x ∈ (M.Lc v).std (D.R.N i))
    (z : MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ) (hz : z ∈ IntSpan D w (X.fm.lam i)) :
    Co.mov w k z ∈ IntSpan D w (X.fm.lam i) := by
  have hl : ∀ v, ∃ g : GL (Fin (D.R.N i)) (Ow D w), Matrix.GeneralLinearGroup.map (embO D w) g =
      Matrix.GeneralLinearGroup.map (D.what₂.embLL.comp (Co.j w v)) (k v) := by
    intro v
    obtain ⟨g, hg⟩ := exists_lift (Ow D w) (Co.j w v) (k v)
      (fun a b => (Co.j_int w hw v _).2 (entry_mem _ (fun x hx => (hk v x).2 hx) a b))
      (fun a b => (Co.j_int w hw v _).2 (entry_mem _ (fun x hx => (hk v _).1 (by
        rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec])) a b))
    refine ⟨g, Units.ext (Matrix.ext fun a b => ?_)⟩
    exact congrArg D.what₂.embLL (hg a b)
  choose g hg using hl
  have := blk_mem_intSpan w (X.fm.lam i) ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)
    (fun τ => if X.fm.seenP w then g ((X.fm.tauOf w).symm τ) else inside₂ _ _ (g ((X.fm.tauOf w).symm τ))) z hz
  have e : ∀ τ, Co.mv w k τ = Matrix.GeneralLinearGroup.map (embO D w)
      (if X.fm.seenP w then g ((X.fm.tauOf w).symm τ) else inside₂ _ _ (g ((X.fm.tauOf w).symm τ))) := by
    intro τ
    unfold PtModel.Coord.mv
    dsimp only
    split_ifs
    · rw [hg]
    · rw [← invTr_map, hg]
  unfold PtModel.Coord.mov PtModel.lamT
  simp only [e]
  exact this

/- English proof (translation)
Introduce `D u X i M Co hCo w hw V p`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: ∀ v, ∃ h, M.IsFrameS v h (if X.fm.seenP w = true ∧ v ∉ V then ((p.2 v).1.L : Set _) else (p.2 v).ker)`. Introduce `v`. Use `split_ifs`.

Conclude with `(p.2 v).2.lat`. Conclude with `exists_frame_ker (p.2 v)`. Use `choose h hh using this`. Conclude with `⟨h, hh, 0, AddSubgroup.zero_mem _, by rw [map_zero, map_zero]⟩`. Introduce and unpack `y ⟨h, hh, z, hz, hy⟩ y' ⟨h', hh', z', hz', hy'⟩`.

Use `⟨h, hh, z + Co.mov w (fun v => (h v)⁻¹ * h' v) z', AddSubgroup.add_mem _ hz (mov_mem Co w hw _ (fun v x => ?_) z' hz'), ?_⟩` and prove the remaining obligations. Rewrite using `[← hh v, ← hh' v x, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]`. Rewrite using `[map_add, map_add, ← mov_mul, hy, hy']`. Simplify using `only [mul_inv_cancel_left]`. Introduce and unpack `r hr y ⟨h, hh, z, hz, hy⟩`.

Conclude with `⟨h, hh, _, smul_mem_intSpan w _ r hr z hz, by rw [map_smul, map_smul, hy]⟩`. Introduce and unpack `g y ⟨h, hh, z, hz, hy⟩`. Take `⟨ζ, k, hk, hζ, hact⟩` from `hCo.act_co w hw g`. Use `⟨fun v => M.loc v g * h v, fun v x => ?_, _, smul_mem_intSpan w _ ζ (mem_Ow_of_pow w ζ k hk hζ) z hz, ?_⟩` and prove the remaining obligations. Rewrite using `[← hh v x, Units.val_mul, ← Matrix.mulVec_mulVec]`.

Establish `ha` using `M.smul_snd g p v (Matrix.mulVec (h v : Matrix _ _ (M.Lc v).K) x)`. Use `split_ifs`. Conclude with `ha.1`. Unfold `LocF.PP.ker`. Simplify using `only [Set.mem_ofPred_eq]`.

Rewrite using `[ha.1, ha.2]`. Rewrite using `[hact, hy, map_smul, mov_mul]`.
-/
theorem valB_laws : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord), Co.Ok → ∀ w, OverT X w → ∀ (V : Finset X.A.vT) (p : M.Pt), (0 : M.Val) ∈ Co.valB w V p ∧ (∀ y ∈ Co.valB w V p, ∀ y' ∈ Co.valB w V p, y + y' ∈ Co.valB w V p) ∧ (∀ r ∈ Ow D w, ∀ y ∈ Co.valB w V p, D.what₂.embLL r • y ∈ Co.valB w V p) ∧ ∀ (g : M.G), ∀ y ∈ Co.valB w V p, M.act g y ∈ Co.valB w V (g • p) := by
  intro D u X i M Co hCo w hw V p
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ∀ v, ∃ h, M.IsFrameS v h
        (if X.fm.seenP w = true ∧ v ∉ V then ((p.2 v).1.L : Set _) else (p.2 v).ker) := by
      intro v
      split_ifs
      · exact (p.2 v).2.lat
      · exact exists_frame_ker (p.2 v)
    choose h hh using this
    exact ⟨h, hh, 0, AddSubgroup.zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro y ⟨h, hh, z, hz, hy⟩ y' ⟨h', hh', z', hz', hy'⟩
    refine ⟨h, hh, z + Co.mov w (fun v => (h v)⁻¹ * h' v) z',
      AddSubgroup.add_mem _ hz (mov_mem Co w hw _ (fun v x => ?_) z' hz'), ?_⟩
    · rw [← hh v, ← hh' v x, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]
    · rw [map_add, map_add, ← mov_mul, hy, hy']
      simp only [mul_inv_cancel_left]
  · rintro r hr y ⟨h, hh, z, hz, hy⟩
    exact ⟨h, hh, _, smul_mem_intSpan w _ r hr z hz, by rw [map_smul, map_smul, hy]⟩
  · rintro g y ⟨h, hh, z, hz, hy⟩
    obtain ⟨ζ, k, hk, hζ, hact⟩ := hCo.act_co w hw g
    refine ⟨fun v => M.loc v g * h v, fun v x => ?_, _,
      smul_mem_intSpan w _ ζ (mem_Ow_of_pow w ζ k hk hζ) z hz, ?_⟩
    · rw [← hh v x, Units.val_mul, ← Matrix.mulVec_mulVec]
      have ha := M.smul_snd g p v (Matrix.mulVec (h v : Matrix _ _ (M.Lc v).K) x)
      split_ifs
      · exact ha.1
      · unfold LocF.PP.ker
        simp only [Set.mem_ofPred_eq]
        rw [ha.1, ha.2]
    · rw [hact, hy, map_smul, mov_mul]

end Main

end GlobalTheory.LvT.ValEq
