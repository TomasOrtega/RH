import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne

noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix
open scoped TensorProduct Classical

namespace GlobalTheory.LKRes

section Generic

variable {G : Type} [Group G]

/- English proof (translation)
Establish `key : ∀ S : Subgroup H, S = ⊤ → ((S.index : ℂ))⁻¹ * ∑ᶠ _q : H ⧸ S, c = c`. Introduce and unpack `S rfl`. Establish `hone : ∀ x : H ⧸ (⊤ : Subgroup H), x = 1` using `fun x => QuotientGroup.induction_on x fun a => (QuotientGroup.eq_one_iff a).2 (Subgroup.mem_top a)`. Rewrite using `[Subgroup.index_top, finsum_eq_single (fun _ => c) (1 : H ⧸ (⊤ : Subgroup H)) (fun x hx => absurd (hone x) hx)]`. Simplify using the standard rewrite rules.

Establish `htop : GlobalTheory.BCT.rStab (fun _ : H => c) = ⊤` using `(Subgroup.eq_top_iff' _).2 fun k => by`. Conclude with `fun x => rfl`. Conclude with `key _ htop`.
-/
theorem avg_const_fun {H : Type} [Group H] (c : ℂ) : GlobalTheory.BCT.avg (fun _ : H => c) = c := by
  have key : ∀ S : Subgroup H, S = ⊤ → ((S.index : ℂ))⁻¹ * ∑ᶠ _q : H ⧸ S, c = c := by
    rintro S rfl
    have hone : ∀ x : H ⧸ (⊤ : Subgroup H), x = 1 := fun x =>
      QuotientGroup.induction_on x fun a => (QuotientGroup.eq_one_iff a).2 (Subgroup.mem_top a)
    rw [Subgroup.index_top, finsum_eq_single (fun _ => c) (1 : H ⧸ (⊤ : Subgroup H))
      (fun x hx => absurd (hone x) hx)]
    simp
  have htop : GlobalTheory.BCT.rStab (fun _ : H => c) = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun k => by
      exact fun x => rfl
  exact key _ htop

/- English proof (translation)
Establish `hmem : ∀ g : G, g ∈ GlobalTheory.BCT.twCent θ δ` using `fun g => h ▸ Subgroup.mem_top g`. Set `q0` to `DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K 1`. Establish `hall : ∀ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G), q = q0`. Introduce `q`. Rewrite using `[← DoubleCoset.out_eq' _ _ q]`.

Conclude with `(DoubleCoset.eq _ _ _ _).2 ⟨(Quotient.out q)⁻¹, hmem _, 1, K.one_mem, by group⟩`. Use `⟨Quotient.out q0, fun w f => ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.LKLoc.orbSum`. Rewrite using `[finsum_eq_single _ q0 (fun q hq => absurd (hall q) hq)]`. Establish `hfix : ∀ g : G, g⁻¹ * δ * θ g = δ`.

Introduce `g`. Establish `hg' : g * δ = δ * θ g` using `hmem g`. Rewrite using `[mul_assoc, ← hg', inv_mul_cancel_left]`. Simplify using `only [hfix, avg_const_fun]`.
-/
theorem orbSum_of_twCent_eq_top (θ : G →* G) (K : Subgroup G) (δ : G) (h : GlobalTheory.BCT.twCent θ δ = ⊤) :
    ∃ x : G, ∀ (w : G → ℝ) (f : G → ℂ), GlobalTheory.LKLoc.orbSum θ K δ w f = (w x : ℂ) * f δ := by
  have hmem : ∀ g : G, g ∈ GlobalTheory.BCT.twCent θ δ := fun g => h ▸ Subgroup.mem_top g
  let q0 := DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K 1
  have hall : ∀ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G), q = q0 := by
    intro q
    rw [← DoubleCoset.out_eq' _ _ q]
    exact (DoubleCoset.eq _ _ _ _).2 ⟨(Quotient.out q)⁻¹, hmem _, 1, K.one_mem, by group⟩
  refine ⟨Quotient.out q0, fun w f => ?_⟩
  unfold GlobalTheory.LKLoc.orbSum
  rw [finsum_eq_single _ q0 (fun q hq => absurd (hall q) hq)]
  have hfix : ∀ g : G, g⁻¹ * δ * θ g = δ := by
    intro g
    have hg' : g * δ = δ * θ g := hmem g
    rw [mul_assoc, ← hg', inv_mul_cancel_left]
  simp only [hfix, avg_const_fun]

/- English proof (translation)
Use `show T ⊓ K.map (MulAut.conj x).toMonoidHom = T ⊓ K`. Use `congr 1`. Use extensionality with `y`. Simplify using `only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `hK.conj_mem k hk x`. Introduce `hy`. Conclude with `⟨x⁻¹ * y * x, by simpa using hK.conj_mem y hy x⁻¹, by group⟩`.
-/
theorem locPart_of_normal (T K : Subgroup G) [hK : K.Normal] (x : G) : GlobalTheory.LKLoc.locPart T K x = T ⊓ K := by
  show T ⊓ K.map (MulAut.conj x).toMonoidHom = T ⊓ K
  congr 1
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hK.conj_mem k hk x
  · intro hy
    exact ⟨x⁻¹ * y * x, by simpa using hK.conj_mem y hy x⁻¹, by group⟩

/- English proof (translation)
Unfold `GlobalTheory.LKLoc.volRat`. Rewrite using `[Subgroup.relIndex_self]`. Simplify using the standard rewrite rules.
-/
private lemma volRat_self' (V : Subgroup G) : GlobalTheory.LKLoc.volRat V V = 1 := by
  unfold GlobalTheory.LKLoc.volRat
  rw [Subgroup.relIndex_self]
  simp

/- English proof (translation)
Unfold `GlobalTheory.LKLoc.twOrbM GlobalTheory.LKLoc.twOrbU`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[locPart_of_normal]`. Unfold `GlobalTheory.LKLoc.maxWt`.

Simplify using `only [locPart_of_normal, volRat_self', ciSup_const]`.
-/
theorem twOrbM_eq_twOrbU_of_normal (θ : G →* G) (K : Subgroup G) [K.Normal] (δ : G) (f : G → ℂ) :
    GlobalTheory.LKLoc.twOrbM θ K δ f = GlobalTheory.LKLoc.twOrbU θ K δ (GlobalTheory.BCT.twCent θ δ ⊓ K) f := by
  unfold GlobalTheory.LKLoc.twOrbM GlobalTheory.LKLoc.twOrbU
  congr 1
  funext x
  rw [locPart_of_normal]
  unfold GlobalTheory.LKLoc.maxWt
  simp only [locPart_of_normal, volRat_self', ciSup_const]

end Generic

variable (p : ℕ) [Fact p.Prime]

abbrev Q0 : IntermediateField ℚ_[p] (PadicAlgCl p) := ⊥

abbrev Qr (r : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) := Kn p (Q0 p) r

def frobQ (r : ℕ) : Qr p r →ₐ[ℚ_[p]] Qr p r :=
  { GlobalTheory.LKLoc.frobR p (Q0 p) r with
    commutes' := fun c => Subtype.ext (((frobK p (Q0 p)).restrictScalars ℚ_[p]).commutes c) }

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def KQ (r : ℕ) : Type := K ⊗[ℚ_[p]] Qr p r

instance (r : ℕ) : CommRing (KQ p K r) := inferInstanceAs (CommRing (K ⊗[ℚ_[p]] Qr p r))

instance (r : ℕ) : Algebra ℚ_[p] (KQ p K r) := inferInstanceAs (Algebra ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))

instance (r : ℕ) : TopologicalSpace (KQ p K r) := moduleTopology ℚ_[p] (KQ p K r)

def inclK (r : ℕ) : K →ₐ[ℚ_[p]] KQ p K r := Algebra.TensorProduct.includeLeft

def inclQ (r : ℕ) : Qr p r →ₐ[ℚ_[p]] KQ p K r := Algebra.TensorProduct.includeRight

def sigKQ (r : ℕ) : KQ p K r →ₐ[ℚ_[p]] KQ p K r :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r)

def intKQ (r : ℕ) : Subring (KQ p K r) :=
  Subring.closure (Set.range (fun a : GlobalTheory.LKLoc.intK p K => inclK p K r a) ∪
    Set.range (fun b : GlobalTheory.LKLoc.intR p (Q0 p) r => inclQ p K r b))

def sigRes (n r : ℕ) : GL (Fin n) (KQ p K r) →* GL (Fin n) (KQ p K r) :=
  GeneralLinearGroup.map (sigKQ p K r).toRingHom

def Kres (n r : ℕ) : Subgroup (GL (Fin n) (KQ p K r)) :=
  (GeneralLinearGroup.map (intKQ p K r).subtype).range

def nrmRes (n r : ℕ) (δ : GL (Fin n) (KQ p K r)) : GL (Fin n) (KQ p K r) :=
  (List.map (fun i => (⇑(sigRes p K n r))^[i] δ) (List.range r)).prod

def twCentRes (n r : ℕ) (δ : GL (Fin n) (KQ p K r)) : Subgroup (GL (Fin n) (KQ p K r)) :=
  GlobalTheory.BCT.twCent (sigRes p K n r) δ

def TORes (n r : ℕ) (δ : GL (Fin n) (KQ p K r)) (φ : GL (Fin n) (KQ p K r) → ℂ) : ℂ :=
  GlobalTheory.LKLoc.twOrbM (sigRes p K n r) (Kres p K n r) δ φ

def TOResU (n r : ℕ) (δ : GL (Fin n) (KQ p K r)) (U : Subgroup (GL (Fin n) (KQ p K r)))
    (φ : GL (Fin n) (KQ p K r) → ℂ) : ℂ :=
  GlobalTheory.LKLoc.twOrbU (sigRes p K n r) (Kres p K n r) δ U φ

abbrev GHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) : Type :=
  GL (Fin 1) (Qr p r) × ((i : Fin m) → GL (Fin n) (KQ p (Kw i) r))

def sigHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) : GHT p m n r Kw →* GHT p m n r Kw :=
  (GlobalTheory.LKLoc.sig p (Q0 p) 1 r).prodMap (Pi.monoidHom fun i => (sigRes p (Kw i) n r).comp (Pi.evalMonoidHom _ i))

def KHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) : Subgroup (GHT p m n r Kw) :=
  (GlobalTheory.LKLoc.Kint p (Q0 p) 1 r).prod (Subgroup.pi Set.univ fun i => Kres p (Kw i) n r)

def twCentHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) (δ : GHT p m n r Kw) :
    Subgroup (GHT p m n r Kw) :=
  GlobalTheory.BCT.twCent (sigHT p m n r Kw) δ

def TOHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) (δ : GHT p m n r Kw)
    (φ : GHT p m n r Kw → ℂ) : ℂ :=
  GlobalTheory.LKLoc.twOrbM (sigHT p m n r Kw) (KHT p m n r Kw) δ φ

def TOHTU (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) (δ : GHT p m n r Kw)
    (U : Subgroup (GHT p m n r Kw)) (φ : GHT p m n r Kw → ℂ) : ℂ :=
  GlobalTheory.LKLoc.twOrbU (sigHT p m n r Kw) (KHT p m n r Kw) δ U φ

/- English proof (translation)
Use `show Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) = a ⊗ₜ[ℚ_[p]] (1 : Qr p r)`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]`.
-/
theorem sigKQ_apply_inclK (r : ℕ) (a : K) : sigKQ p K r (inclK p K r a) = inclK p K r a := by
  show Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) =
    a ⊗ₜ[ℚ_[p]] (1 : Qr p r)
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

/- English proof (translation)
Use `show Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) ((1 : K) ⊗ₜ[ℚ_[p]] b) = (1 : K) ⊗ₜ[ℚ_[p]] (frobQ p r b)`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`.
-/
theorem sigKQ_apply_inclQ (r : ℕ) (b : Qr p r) : sigKQ p K r (inclQ p K r b) = inclQ p K r (frobQ p r b) := by
  show Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) ((1 : K) ⊗ₜ[ℚ_[p]] b) =
    (1 : K) ⊗ₜ[ℚ_[p]] (frobQ p r b)
  rw [Algebra.TensorProduct.map_tmul, map_one]

/- English proof (translation)
Establish `hK : FiniteDimensional ℚ_[p] (Q0 p)` using `by infer_instance`. Establish `hle : Q0 p ≤ Qr p 1` using `bot_le`. Establish `hdeg : degLK p (Q0 p) (Kn p (Q0 p) 1) = 1` using `degLK_Kn hK one_pos`. Rewrite `hdeg` using `[degLK_eq_finrank (h := hle)]`. Establish `hbot` using `IntermediateField.finrank_eq_one_iff.1 hdeg`.

Use `AlgHom.ext fun x => Subtype.ext ?_` and prove the remaining obligations. Establish `hx : (x : PadicAlgCl p) ∈ Q0 p`. Establish `h1 : (x : PadicAlgCl p) ∈ IntermediateField.extendScalars hle`. Conclude with `x.2`. Rewrite `h1` using `[hbot]`.

Take `⟨y, hy⟩` from `IntermediateField.mem_bot.1 h1`. Rewrite using `[← hy]`. Conclude with `y.2`. Conclude with `(frobK p (Q0 p)).commutes ⟨_, hx⟩`.
-/
theorem frobQ_degree_one : frobQ p 1 = AlgHom.id ℚ_[p] (Qr p 1) := by
  have hK : FiniteDimensional ℚ_[p] (Q0 p) := by
    infer_instance
  have hle : Q0 p ≤ Qr p 1 := bot_le
  have hdeg : degLK p (Q0 p) (Kn p (Q0 p) 1) = 1 := degLK_Kn hK one_pos
  rw [degLK_eq_finrank (h := hle)] at hdeg
  have hbot := IntermediateField.finrank_eq_one_iff.1 hdeg
  refine AlgHom.ext fun x => Subtype.ext ?_
  have hx : (x : PadicAlgCl p) ∈ Q0 p := by
    have h1 : (x : PadicAlgCl p) ∈ IntermediateField.extendScalars hle := by
      exact x.2
    rw [hbot] at h1
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 h1
    rw [← hy]
    exact y.2
  exact (frobK p (Q0 p)).commutes ⟨_, hx⟩

/- English proof (translation)
Establish `h1 : sigKQ p K 1 = AlgHom.id ℚ_[p] (KQ p K 1)`. Unfold `sigKQ`. Rewrite using `[frobQ_degree_one]`. Conclude with `Algebra.TensorProduct.map_id`. Use `MonoidHom.ext fun g => Matrix.GeneralLinearGroup.ext fun i j => ?_` and prove the remaining obligations.

Use `show sigKQ p K 1 ((g : Matrix (Fin n) (Fin n) (KQ p K 1)) i j) = (g : Matrix (Fin n) (Fin n) (KQ p K 1)) i j`. Rewrite using `[h1]`. Both sides reduce to the same expression.
-/
theorem sigRes_degree_one (n : ℕ) : sigRes p K n 1 = MonoidHom.id _ := by
  have h1 : sigKQ p K 1 = AlgHom.id ℚ_[p] (KQ p K 1) := by
    unfold sigKQ
    rw [frobQ_degree_one]
    exact Algebra.TensorProduct.map_id
  refine MonoidHom.ext fun g => Matrix.GeneralLinearGroup.ext fun i j => ?_
  show sigKQ p K 1 ((g : Matrix (Fin n) (Fin n) (KQ p K 1)) i j) = (g : Matrix (Fin n) (Fin n) (KQ p K 1)) i j
  rw [h1]
  rfl

/- English proof (translation)
Use `Matrix.GeneralLinearGroup.ext fun i j => ?_` and prove the remaining obligations. Use `fin_cases i`. Use `fin_cases j`. Simplify using `[Matrix.mul_apply, mul_comm]`.
-/
private lemma gl_fin_one_mul_comm {R : Type} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun n hn g => by rw [gl_fin_one_mul_comm g n, mul_inv_cancel_right] exact hn⟩`.
-/
theorem normal_of_gl_one {R : Type} [CommRing R] (H : Subgroup (GL (Fin 1) R)) : H.Normal :=
  ⟨fun n hn g => by
    rw [gl_fin_one_mul_comm g n, mul_inv_cancel_right]
    exact hn⟩

/- English proof (translation)
Establish `hc : ∀ a b : GHT p m 1 r Kw, a * b = b * a` using `fun a b => Prod.ext (gl_fin_one_mul_comm _ _) (funext fun i => gl_fin_one_mul_comm _ _)`. Establish `: (KHT p m 1 r Kw).Normal` using `⟨fun n hn g => by`. Rewrite using `[hc g n, mul_inv_cancel_right]`. Conclude with `hn⟩`. Conclude with `twOrbM_eq_twOrbU_of_normal (sigHT p m 1 r Kw) (KHT p m 1 r Kw) δ φ`.
-/
theorem TOHT_gl_one (m r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) (δ : GHT p m 1 r Kw)
    (φ : GHT p m 1 r Kw → ℂ) :
    TOHT p m 1 r Kw δ φ = TOHTU p m 1 r Kw δ (twCentHT p m 1 r Kw δ ⊓ KHT p m 1 r Kw) φ := by
  have hc : ∀ a b : GHT p m 1 r Kw, a * b = b * a := fun a b =>
    Prod.ext (gl_fin_one_mul_comm _ _) (funext fun i => gl_fin_one_mul_comm _ _)
  have : (KHT p m 1 r Kw).Normal :=
    ⟨fun n hn g => by
      rw [hc g n, mul_inv_cancel_right]
      exact hn⟩
  exact twOrbM_eq_twOrbU_of_normal (sigHT p m 1 r Kw) (KHT p m 1 r Kw) δ φ

/- English proof (translation)
Simplify using `[nrmRes]`.
-/
example (δ : GL (Fin 2) (KQ p K 1)) : nrmRes p K 2 1 δ = δ := by simp [nrmRes]

/- English proof (translation)
Simplify using `[nrmRes, List.range_succ]`.
-/
example (δ : GL (Fin 2) (KQ p K 2)) : nrmRes p K 2 2 δ = δ * sigRes p K 2 2 δ := by
  simp [nrmRes, List.range_succ]

/- English proof (translation)
Unfold `KQ`. Use `infer_instance`.
-/
example (r : ℕ) : Nontrivial (KQ p K r) := by unfold KQ; infer_instance

end GlobalTheory.LKRes
