import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtExB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealPlaceEmbeddings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticLatticeForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelB

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate

noncomputable section

namespace TX

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

open Classical in

def dimT (σ : E →+* ℂ) : ℕ := if σ ∈ X.Ψ then X.p0 else r - X.p0

/- English proof (translation)
Rewrite using `[← X.conj_mem_iff, Data.conjugate_conjugate']`. Conclude with `τ.2`.
-/
theorem conj_notMem (τ : X.Ψ) : ComplexEmbedding.conjugate τ.1 ∉ X.Ψ := by
  rw [← X.conj_mem_iff, Data.conjugate_conjugate']; exact τ.2

/- English proof (translation)
Simplify using `[dimT, h]`.
-/
theorem dimT_of_mem {σ : E →+* ℂ} (h : σ ∈ X.Ψ) : dimT X σ = X.p0 := by
  classical
  simp [dimT, h]

/- English proof (translation)
Simplify using `[dimT, h]`.
-/
theorem dimT_of_notMem {σ : E →+* ℂ} (h : σ ∉ X.Ψ) : dimT X σ = r - X.p0 := by
  classical
  simp [dimT, h]

/- English proof (translation)
Unfold `dimT`. Use `split_ifs`. Conclude with `X.p0_le`. Use linear arithmetic over natural numbers and integers.
-/
theorem dimT_le (σ : E →+* ℂ) : dimT X σ ≤ r := by
  classical
  unfold dimT; split_ifs
  · exact X.p0_le
  · omega

/- English proof (translation)
Distinguish the cases in `h : σ ∈ X.Ψ`. Establish `h' : ComplexEmbedding.conjugate σ ∉ X.Ψ` using `by rw [X.conj_mem_iff]; exact not_not.mpr h`. Rewrite using `[dimT_of_mem X h, dimT_of_notMem X h']`. Use `X.p0_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `h' : ComplexEmbedding.conjugate σ ∈ X.Ψ` using `(X.conj_mem_iff σ).mpr h`. Rewrite using `[dimT_of_notMem X h, dimT_of_mem X h']`. Use `X.p0_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem dimT_conj (σ : E →+* ℂ) : dimT X σ + dimT X (ComplexEmbedding.conjugate σ) = r := by
  by_cases h : σ ∈ X.Ψ
  · have h' : ComplexEmbedding.conjugate σ ∉ X.Ψ := by rw [X.conj_mem_iff]; exact not_not.mpr h
    rw [dimT_of_mem X h, dimT_of_notMem X h']; have := X.p0_le; omega
  · have h' : ComplexEmbedding.conjugate σ ∈ X.Ψ := (X.conj_mem_iff σ).mpr h
    rw [dimT_of_notMem X h, dimT_of_mem X h']; have := X.p0_le; omega

def psiOf (σ : E →+* ℂ) (h : σ ∉ X.Ψ) : X.Ψ := ⟨ComplexEmbedding.conjugate σ, (X.conj_mem_iff σ).mpr h⟩

/- English proof (translation)
The claim follows from `Subtype.ext (Data.conjugate_conjugate' τ.1)`.
-/
theorem psiOf_conj (τ : X.Ψ) : psiOf X (ComplexEmbedding.conjugate τ.1) (conj_notMem X τ) = τ :=
  Subtype.ext (Data.conjugate_conjugate' τ.1)

/- English proof (translation)
Simplify using `only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
theorem hermC_add_left (τ : E →+* ℂ) (u u' v : Fin r → ℂ) :
    hermC τ X.Gm (u + u') v = hermC τ X.Gm u v + hermC τ X.Gm u' v := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`.
-/
theorem hermC_smul_left (τ : E →+* ℂ) (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ X.Gm (c • u) v = c * hermC τ X.Gm u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hermC]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermC_add_left, ih]`.
-/
theorem hermC_sum_left (τ : E →+* ℂ) {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ X.Gm (∑ i ∈ s, f i) v = ∑ i ∈ s, hermC τ X.Gm (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermC]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermC_add_left, ih]

variable (e : X.Ψ → Fin r → (Fin r → ℂ))

/- English proof (translation)
Establish `h1` using `dimT_of_notMem X h`. Use `a.2` as an intermediate fact. Use `X.p0_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem neg_lt (σ : E →+* ℂ) (h : σ ∉ X.Ψ) (a : Fin (dimT X σ)) : X.p0 + a.1 < r := by
  have h1 := dimT_of_notMem X h
  have := a.2; have := X.p0_le; omega

open Classical in

def coordF (u : X.Ψ → Fin r → ℂ) (i : Idx (dimT X)) : ℂ :=
  if h : i.1 ∈ X.Ψ then
    (Real.sqrt (X.c ⟨i.1, h⟩) : ℂ) *
      hermC i.1 X.Gm (u ⟨i.1, h⟩) (e ⟨i.1, h⟩ ⟨i.2.1, lt_of_lt_of_le i.2.2 (dimT_le X i.1)⟩)
  else
    (Real.sqrt (X.c (psiOf X i.1 h)) : ℂ) *
      conj (-hermC (psiOf X i.1 h).1 X.Gm (u (psiOf X i.1 h))
        (e (psiOf X i.1 h) ⟨X.p0 + i.2.1, neg_lt X i.1 h i.2⟩))

def Lc : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] Vsp (dimT X) where
  toFun u := WithLp.toLp 2 (coordF X e u)
  map_add' u u' := by
    ext i
    simp only [coordF, Pi.add_apply, WithLp.toLp_add, PiLp.add_apply]
    split_ifs <;> simp [hermC_add_left, mul_add] <;> ring
  map_smul' c u := by
    ext i
    simp only [coordF, Pi.smul_apply, RingHom.id_apply, PiLp.smul_apply, WithLp.toLp_smul]
    have hc : ∀ w : Fin r → ℂ, c • w = (c : ℂ) • w := fun w => rfl
    split_ifs
    · rw [hc, hermC_smul_left]; simp [Complex.real_smul]; ring
    · rw [hc, hermC_smul_left]; simp [Complex.real_smul]; ring

/- English proof (translation)
Use `show coordF X e u ⟨τ.1, a⟩ = _`. Simplify using `only [coordF, dif_pos τ.2]`.
-/
theorem Lc_pos (u : X.Ψ → Fin r → ℂ) (τ : X.Ψ) (a : Fin (dimT X τ.1)) :
    Lc X e u ⟨τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) *
      hermC τ.1 X.Gm (u τ) (e τ ⟨a.1, lt_of_lt_of_le a.2 (dimT_le X τ.1)⟩) := by
  show coordF X e u ⟨τ.1, a⟩ = _
  simp only [coordF, dif_pos τ.2]

/- English proof (translation)
Use `show coordF X e u ⟨ComplexEmbedding.conjugate τ.1, a⟩ = _`. Simplify using `only [coordF, dif_neg (conj_notMem X τ)]`. Rewrite using `[psiOf_conj]`.
-/
theorem Lc_neg (u : X.Ψ → Fin r → ℂ) (τ : X.Ψ) (a : Fin (dimT X (ComplexEmbedding.conjugate τ.1))) :
    Lc X e u ⟨ComplexEmbedding.conjugate τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) *
      conj (-hermC τ.1 X.Gm (u τ) (e τ ⟨X.p0 + a.1, neg_lt X _ (conj_notMem X τ) a⟩)) := by
  show coordF X e u ⟨ComplexEmbedding.conjugate τ.1, a⟩ = _
  simp only [coordF, dif_neg (conj_notMem X τ)]
  rw [psiOf_conj]

variable {X e}

/- English proof (translation)
Apply the tactic sequence `unfold sgn; split_ifs <;> norm_num`.
-/
theorem sgn_ne (a : ℕ) : ((sgn X.p0 a : ℝ) : ℂ) ≠ 0 := by
  unfold sgn; split_ifs <;> norm_num

/- English proof (translation)
Simplify using `[hermC]`.
-/
theorem hermC_zero_left (τ : E →+* ℂ) (v : Fin r → ℂ) : hermC τ X.Gm 0 v = 0 := by simp [hermC]

def IsOF (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) : Prop :=
  ∀ τ : X.Ψ, ∀ a b, hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0

/- English proof (translation)
Rewrite using `[hermC_sum_left]`. Simplify using `only [hermC_smul_left, he τ, mul_ite, mul_zero]`. Rewrite using `[Finset.sum_ite_eq' Finset.univ a]`. Simplify using the standard rewrite rules.
-/
theorem hermC_comb (he : IsOF X e) (τ : X.Ψ) (d : Fin r → ℂ) (a : Fin r) :
    hermC τ.1 X.Gm (∑ j, d j • e τ j) (e τ a) = d a * ((sgn X.p0 a : ℝ) : ℂ) := by
  rw [hermC_sum_left]
  simp only [hermC_smul_left, he τ, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ a]
  simp

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Establish `h` using `congrArg (fun w => hermC τ.1 X.Gm w (e τ i)) hg`. Rewrite `h` using `[hermC_comb he τ g i, hermC_zero_left]`. Conclude with `(mul_eq_zero.mp h).resolve_right (sgn_ne i)`.
-/
theorem e_linInd (he : IsOF X e) (τ : X.Ψ) : LinearIndependent ℂ (e τ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (fun w => hermC τ.1 X.Gm w (e τ i)) hg
  rw [hermC_comb he τ g i, hermC_zero_left] at h
  exact (mul_eq_zero.mp h).resolve_right (sgn_ne i)

/- English proof (translation)
Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[finrank_span_eq_card hf, hc]`.
-/
theorem span_top_of_linInd {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] {f : ι → V} (hf : LinearIndependent K f) (hc : Fintype.card ι = Module.finrank K V) :
    Submodule.span K (Set.range f) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card hf, hc]

/- English proof (translation)
Establish `hsp : Submodule.span ℂ (Set.range (e τ)) = ⊤` using `span_top_of_linInd (e_linInd he τ) (by simp)`. Establish `hwm : w ∈ Submodule.span ℂ (Set.range (e τ))` using `hsp ▸ Submodule.mem_top`. Take `⟨d, hd⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).mp hwm`. Establish `hd0 : ∀ a, d a = 0`. Introduce `a`.

Establish `h` using `hw a`. Rewrite `h` using `[← hd, hermC_comb he τ d a]`. Conclude with `(mul_eq_zero.mp h).resolve_right (sgn_ne a)`. Rewrite using `[← hd]`. Simplify using `[hd0]`.
-/
theorem eq_zero_of_hermC (he : IsOF X e) (τ : X.Ψ) (w : Fin r → ℂ)
    (hw : ∀ a, hermC τ.1 X.Gm w (e τ a) = 0) : w = 0 := by
  have hsp : Submodule.span ℂ (Set.range (e τ)) = ⊤ := span_top_of_linInd (e_linInd he τ) (by simp)
  have hwm : w ∈ Submodule.span ℂ (Set.range (e τ)) := hsp ▸ Submodule.mem_top
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hwm
  have hd0 : ∀ a, d a = 0 := by
    intro a
    have h := hw a
    rw [← hd, hermC_comb he τ d a] at h
    exact (mul_eq_zero.mp h).resolve_right (sgn_ne a)
  rw [← hd]; simp [hd0]

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `u hu`. Use function extensionality and compare the values at `τ`. Use `show u τ = 0`. Apply `eq_zero_of_hermC he τ` to reduce the goal to its premises.

Introduce `a`. Establish `hsc : (Real.sqrt (X.c τ) : ℂ) ≠ 0`. Conclude with `(Real.sqrt_pos.mpr (QuadraticLatticeForms.c_pos X τ)).ne'` after adjusting the coercions. Distinguish the cases in `ha : (a : ℕ) < X.p0`. Establish `h` using `congrArg (fun y : Vsp (dimT X) => y ⟨τ.1, ⟨a.1, by rw [dimT_of_mem X τ.2]; exact ha⟩⟩) hu`.

Simplify using `only [Lc_pos, PiLp.zero_apply] at h`. Conclude with `(mul_eq_zero.mp h).resolve_left hsc`. Establish `hlt : a.1 - X.p0 < dimT X (ComplexEmbedding.conjugate τ.1)`. Rewrite using `[dimT_of_notMem X (conj_notMem X τ)]`. Use `a.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h` using `congrArg (fun y : Vsp (dimT X) => y ⟨ComplexEmbedding.conjugate τ.1, ⟨a.1 - X.p0, hlt⟩⟩) hu`. Simplify using `only [Lc_neg, PiLp.zero_apply] at h`. Establish `hidx : (⟨X.p0 + (a.1 - X.p0), neg_lt X _ (conj_notMem X τ) ⟨a.1 - X.p0, hlt⟩⟩ : Fin r) = a` using `Fin.ext (by simp only; omega)`. Rewrite `h` using `[hidx]`.

Establish `h2` using `(mul_eq_zero.mp h).resolve_left hsc`. Simplify using `using h2`.
-/
theorem Lc_injective (he : IsOF X e) : Function.Injective (Lc X e) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  funext τ
  show u τ = 0
  apply eq_zero_of_hermC he τ
  intro a
  have hsc : (Real.sqrt (X.c τ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (QuadraticLatticeForms.c_pos X τ)).ne'
  by_cases ha : (a : ℕ) < X.p0
  · have h := congrArg (fun y : Vsp (dimT X) => y ⟨τ.1, ⟨a.1, by rw [dimT_of_mem X τ.2]; exact ha⟩⟩) hu
    simp only [Lc_pos, PiLp.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_left hsc
  · have hlt : a.1 - X.p0 < dimT X (ComplexEmbedding.conjugate τ.1) := by
      rw [dimT_of_notMem X (conj_notMem X τ)]; have := a.2; omega
    have h := congrArg (fun y : Vsp (dimT X) => y ⟨ComplexEmbedding.conjugate τ.1, ⟨a.1 - X.p0, hlt⟩⟩) hu
    simp only [Lc_neg, PiLp.zero_apply] at h
    have hidx : (⟨X.p0 + (a.1 - X.p0), neg_lt X _ (conj_notMem X τ) ⟨a.1 - X.p0, hlt⟩⟩ : Fin r) = a :=
      Fin.ext (by simp only; omega)
    rw [hidx] at h
    have h2 := (mul_eq_zero.mp h).resolve_left hsc
    simpa using h2

variable (X) in
/- English proof (translation)
Rewrite using `[Fintype.card_sigma]`. Simplify using `only [Fintype.card_fin]`. Establish `h` using `X.sum_emb_split (fun σ => ((dimT X σ : ℕ) : ℂ))`. Establish `h2 : ∑ τ : X.Ψ, (((dimT X τ.1 : ℕ) : ℂ) + ((dimT X (ComplexEmbedding.conjugate τ.1) : ℕ) : ℂ)) = ((Fintype.card X.Ψ * r : ℕ) : ℂ)`. Simplify using `only [← Nat.cast_add, dimT_conj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[h2]`. Conclude with `h` after adjusting the coercions.
-/
theorem card_idx : Fintype.card (Idx (dimT X)) = Fintype.card X.Ψ * r := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have h := X.sum_emb_split (fun σ => ((dimT X σ : ℕ) : ℂ))
  have h2 : ∑ τ : X.Ψ, (((dimT X τ.1 : ℕ) : ℂ) + ((dimT X (ComplexEmbedding.conjugate τ.1) : ℕ) : ℂ)) =
      ((Fintype.card X.Ψ * r : ℕ) : ℂ) := by
    simp only [← Nat.cast_add, dimT_conj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    push_cast; ring
  rw [h2] at h
  exact_mod_cast h

variable (X) in
/- English proof (translation)
Establish `b` using `Module.Basis.mk (RealPlaceEmbeddings.linIndR X (RealPlaceEmbeddings.zb X)) (RealPlaceEmbeddings.span_embV X (RealPlaceEmbeddings.zb X)).ge`. Establish `h` using `Module.finrank_eq_card_basis b`. Simplify using `only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h`. Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_Λ : Module.finrank ℤ X.Λ = 2 * (Fintype.card X.Ψ * r) := by
  have b := Module.Basis.mk (RealPlaceEmbeddings.linIndR X (RealPlaceEmbeddings.zb X)) (RealPlaceEmbeddings.span_embV X (RealPlaceEmbeddings.zb X)).ge
  have h := Module.finrank_eq_card_basis b
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  rw [← h]; ring

variable (X) in
/- English proof (translation)
The claim follows from `cab_finrank`.
-/
theorem finrank_V : Module.finrank ℝ (Vsp (dimT X)) = 2 * Fintype.card (Idx (dimT X)) := cab_finrank

/- English proof (translation)
The claim follows from `(RealPlaceEmbeddings.linIndR X (RealPlaceEmbeddings.zb X)).map' (Lc X e) (LinearMap.ker_eq_bot.mpr (Lc_injective he))`.
-/
theorem linInd_V (he : IsOF X e) :
    LinearIndependent ℝ (fun i => Lc X e (X.embV (RealPlaceEmbeddings.zb X i : Fin r → E))) :=
  (RealPlaceEmbeddings.linIndR X (RealPlaceEmbeddings.zb X)).map' (Lc X e) (LinearMap.ker_eq_bot.mpr (Lc_injective he))

variable (X) in
/- English proof (translation)
Rewrite using `[Fintype.card_fin, finrank_Λ, finrank_V, card_idx]`.
-/
theorem card_eq : Fintype.card (Fin (Module.finrank ℤ X.Λ)) = Module.finrank ℝ (Vsp (dimT X)) := by
  rw [Fintype.card_fin, finrank_Λ, finrank_V, card_idx]

/- English proof (translation)
The claim follows from `span_top_of_linInd (linInd_V he) (card_eq X)`.
-/
theorem span_V (he : IsOF X e) :
    Submodule.span ℝ (Set.range (fun i => Lc X e (X.embV (RealPlaceEmbeddings.zb X i : Fin r → E)))) = ⊤ :=
  span_top_of_linInd (linInd_V he) (card_eq X)

def bV (he : IsOF X e) : Module.Basis (Fin (Module.finrank ℤ X.Λ)) ℝ (Vsp (dimT X)) :=
  Module.Basis.mk (linInd_V he) (span_V he).ge

variable (X) in
/- English proof (translation)
Rewrite using `[finrank_Λ, card_idx]`.
-/
theorem card_eq' : Module.finrank ℤ X.Λ = 2 * Fintype.card (Idx (dimT X)) := by
  rw [finrank_Λ, card_idx]

def bT (he : IsOF X e) : Module.Basis (Fin (2 * Fintype.card (Idx (dimT X)))) ℝ (Vsp (dimT X)) :=
  (bV he).reindex (finCongr (card_eq' X))

variable (X e) in

def phi : (Fin r → E) →+ Vsp (dimT X) where
  toFun v := Lc X e (X.embV v)
  map_zero' := by
    have : X.embV (0 : Fin r → E) = 0 := by funext τ a; simp [Data.embV, Data.emb]
    rw [this, map_zero]
  map_add' u v := by
    have : X.embV (u + v) = X.embV u + X.embV v := by funext τ a; simp [Data.embV, Data.emb]
    rw [this, map_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phi_apply (v : Fin r → E) : phi X e v = Lc X e (X.embV v) := rfl

end TX

end

end ReciprocityTheory.ChartRestriction.G.I2
