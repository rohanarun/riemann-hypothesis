module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabiliserSplitPlace
section
noncomputable section

namespace GlobalTheory.Core.Rk.IwFlagSplit

section Pure

variable {A R : Type} [CommRing A] [CommRing R] {n ρ s : Type} [Fintype n] [Fintype ρ] [Fintype s] [DecidableEq n]
  [DecidableEq ρ] [DecidableEq s]

theorem map_keeps (f : A →+* R) {M : Matrix n n A} {j : Matrix n ρ A} {p : Matrix ρ n A} (hp : p * j = 1)
    {a : Matrix ρ ρ R} (h : M.map f * j.map f = j.map f * a) : (M * j).map f = (j * (p * (M * j))).map f := by
  have h1 : p.map f * j.map f = 1 := by rw [← Matrix.map_mul, hp, Matrix.map_one _ (map_zero f) (map_one f)]
  rw [Matrix.map_mul (L := j), Matrix.map_mul (L := p), Matrix.map_mul, h, ← Matrix.mul_assoc (p.map f), h1,
    Matrix.one_mul]

def lev : (ρ ⊕ s) ⊕ ρ → ℕ := Sum.elim (Sum.elim (fun _ => 0) fun _ => 1) fun _ => 2


omit [DecidableEq ρ] [DecidableEq s] in
theorem keeps_cols (ε : n ≃ (ρ ⊕ s) ⊕ ρ) {e e' : Matrix n ρ A} {i : Matrix n s A} {B b : GL n A}
    (hB : B.1 = (Matrix.fromCols (Matrix.fromCols e i) e').submatrix id ε) (hb : b.1.BlockTriangular (lev ∘ ε)) :
    ∃ a : Matrix ρ ρ A, (B * b * B⁻¹).1 * e = e * a := by
  refine ⟨Matrix.of fun k l => b.1 (ε.symm (.inl (.inl k))) (ε.symm (.inl (.inl l))), ?_⟩
  have h : (B * b * B⁻¹).1 * B.1 = B.1 * b.1 := by rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
  generalize (B * b * B⁻¹).1 = x at h
  ext k l
  have h1 := congrFun (congrFun h k) (ε.symm (.inl (.inl l)))
  have h2 : ∀ t, b.1 (ε.symm (.inl (.inr t))) (ε.symm (.inl (.inl l))) = 0 := fun t => hb (by simp [lev])
  have h3 : ∀ t, b.1 (ε.symm (.inr t)) (ε.symm (.inl (.inl l))) = 0 := fun t => hb (by simp [lev])
  rw [hB, Matrix.mul_apply, Matrix.mul_apply, ← ε.symm.sum_comp fun t => _ * b.1 t _] at h1
  simpa [Matrix.mul_apply, h2, h3] using h1


omit [DecidableEq ρ] [DecidableEq s] in
theorem keeps_rows (ε : n ≃ (ρ ⊕ s) ⊕ ρ) {p p' : Matrix ρ n A} {q : Matrix s n A} {B b : GL n A}
    (hB : (B⁻¹).1 = (Matrix.fromRows (Matrix.fromRows p q) p').submatrix ε id) (hb : b.1.BlockTriangular (lev ∘ ε)) :
    ∃ c : Matrix ρ ρ A, p' * (B * b * B⁻¹).1 = c * p' := by
  refine ⟨Matrix.of fun k l => b.1 (ε.symm (.inr k)) (ε.symm (.inr l)), ?_⟩
  have h : (B⁻¹).1 * (B * b * B⁻¹).1 = b.1 * (B⁻¹).1 := by
    rw [← Units.val_mul, mul_assoc, inv_mul_cancel_left, Units.val_mul]
  generalize (B * b * B⁻¹).1 = x at h
  ext k l
  have h1 := congrFun (congrFun h (ε.symm (.inr k))) l
  have h2 : ∀ t, b.1 (ε.symm (.inr k)) (ε.symm (.inl t)) = 0 := fun t => hb (by rcases t with t | t <;> simp [lev])
  rw [hB, Matrix.mul_apply, Matrix.mul_apply, ← ε.symm.sum_comp fun t => b.1 _ t * _] at h1
  simpa [Matrix.mul_apply, h2] using h1


omit [DecidableEq s] [Fintype s] in
theorem keeps_dual {G x x' : Matrix n n A} {e f : Matrix n ρ A} {c : Matrix ρ ρ A} {xi Gi : Matrix n n A}
    (hx : x * xi = 1) (hG : G * Gi = 1) (h : x'.transpose * G * x = G) (hf : e.transpose * G * f = 1)
    (hc : e.transpose * G * x = c * (e.transpose * G)) : ∃ a : Matrix ρ ρ A, x' * e = e * a := by
  have h1 : e.transpose * G = c * (e.transpose * G * xi) := by
    rw [← Matrix.mul_assoc, ← hc, Matrix.mul_assoc _ x, hx, Matrix.mul_one]
  have h2 : c * (e.transpose * G * xi * f) = 1 := by rw [← Matrix.mul_assoc, ← h1, hf]
  have h3 := mul_eq_one_comm.1 h2
  generalize e.transpose * G * xi * f = c' at h3
  have h4 : e.transpose * G * xi = c' * (e.transpose * G) := by
    rw [h1, ← Matrix.mul_assoc c', h3, Matrix.one_mul, ← h1]
  have h5 : x'.transpose * G = G * xi := by
    conv_rhs => rw [← h, Matrix.mul_assoc, hx, Matrix.mul_one]
  refine ⟨c'.transpose, Matrix.transpose_injective ?_⟩
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mul_one (e.transpose * _), ← hG, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ G, h5, ← Matrix.mul_assoc, h4,
    Matrix.mul_assoc, Matrix.mul_assoc, hG, Matrix.mul_one]

end Pure

section Local

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (bc GLint)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)} {ρ s : Type} [Fintype ρ] [Fintype s] [DecidableEq ρ]
  [DecidableEq s]

theorem emb_keeps (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (q : GLoc σ J v) {j : Matrix (Fin n) ρ (AF F ⊗[F] E)}
    {p : Matrix ρ (Fin n) (AF F ⊗[F] E)} (hp : p * j = 1) {e : Matrix (Fin n) ρ E} (hj : j = e.map (inclR (AF F)))
    {a a' : Matrix ρ ρ (Fv F v)} (h1 : (splitHom σ J τ q).1 * e.map τ = e.map τ * a)
    (h2 : (splitHom σ J (τ.comp σ) q).1 * e.map (τ.comp σ) = e.map (τ.comp σ) * a') :
    (matHom _ σ J (emb σ J v q)).1 * j = j * (p * ((matHom _ σ J (emb σ J v q)).1 * j)) := by
  have key : ∀ (τ : E →ₐ[F] Fv F v) {a : Matrix ρ ρ (Fv F v)}, (splitHom σ J τ q).1 * e.map τ = e.map τ * a →
      (matHom _ σ J (emb σ J v q)).1.map (((splitProj τ).toRingHom).comp (compFin F E v)) *
        j.map (((splitProj τ).toRingHom).comp (compFin F E v)) =
        j.map (((splitProj τ).toRingHom).comp (compFin F E v)) * a := fun τ a ha => by
    have e1 : (matHom _ σ J (emb σ J v q)).1.map (((splitProj τ).toRingHom).comp (compFin F E v)) =
        (splitHom σ J τ q).1 := by
      conv_rhs => rw [← proj_emb_self σ J v q]
      rfl
    have e2 : j.map (((splitProj τ).toRingHom).comp (compFin F E v)) = e.map τ := by
      ext k l
      simp [hj, inclR, compFin]
    rw [e1, e2, ha]
  ext k l
  refine GlobalTheory.Doubling.adele_ext (fun w => ?_) fun u => ?_
  · have e1 : (matHom _ σ J (emb σ J v q)).1.map (compInf F E w) = 1 := by
      change (matHom _ σ J (projArch σ J w (emb σ J v q))).1 = 1
      rw [projArch_emb, map_one, Units.val_one]
    exact congrFun (congrFun (map_keeps (compInf F E w) hp (a := 1) (by rw [e1, Matrix.one_mul, Matrix.mul_one])) k) l
  · by_cases hu : u = v
    · subst hu
      exact split_ext h τ (congrFun (congrFun (map_keeps _ hp (key τ h1)) k) l)
        (congrFun (congrFun (map_keeps _ hp (key _ h2)) k) l)
    · have e1 : (matHom _ σ J (emb σ J v q)).1.map (compFin F E u) = 1 := by
        change (matHom _ σ J (proj σ J u (emb σ J v q))).1 = 1
        rw [proj_emb_ne σ J hu, map_one, Units.val_one]
      exact congrFun (congrFun (map_keeps (compFin F E u) hp (a := 1) (by rw [e1, Matrix.one_mul, Matrix.mul_one])) k) l

theorem exists_flag_basis (τ : E →ₐ[F] Fv F v) (hJ : IsHermND σ J) {e e' : Matrix (Fin n) ρ E}
    {i : Matrix (Fin n) s E} {p : Matrix ρ (Fin n) E} {q : Matrix s (Fin n) E} (ε : Fin n ≃ (ρ ⊕ s) ⊕ ρ)
    (hsum : e * p + i * q + e' * ((e.map σ)ᵀ * J) = 1) (hf : (e.map σ)ᵀ * J * e' = 1) :
    ∃ (B : GL (Fin n) (Fv F v)) (lv : Fin n → ℕ), ∀ g : GLoc σ J v, (B⁻¹ * splitHom σ J τ g * B).1.BlockTriangular lv →
      (∃ a : Matrix ρ ρ (Fv F v), (splitHom σ J τ g).1 * e.map τ = e.map τ * a) ∧
        ∃ a : Matrix ρ ρ (Fv F v), (splitHom σ J (τ.comp σ) g).1 * e.map (τ.comp σ) = e.map (τ.comp σ) * a := by
  have hm : ((e.map σ)ᵀ * J).map τ = (e.map (τ.comp σ))ᵀ * J.map τ := Matrix.map_mul (f := (τ : E →+* Fv F v))
  have hB : (Matrix.fromCols (Matrix.fromCols (e.map τ) (i.map τ)) (e'.map τ)).submatrix id ε *
      (Matrix.fromRows (Matrix.fromRows (p.map τ) (q.map τ)) ((e.map (τ.comp σ))ᵀ * J.map τ)).submatrix ε id = 1 := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows,
      ← hm]
    have := congrArg (τ : E →+* Fv F v).mapMatrix hsum
    rw [map_add (f := _), map_add (f := _), map_one] at this
    simp only [RingHom.mapMatrix_apply, Matrix.map_mul] at this
    rw [hm]
    exact this
  refine ⟨⟨_, _, hB, mul_eq_one_comm.1 hB⟩, lev ∘ ε, fun g hg => ?_⟩
  generalize hBe : (⟨_, _, hB, mul_eq_one_comm.1 hB⟩ : GL (Fin n) (Fv F v)) = B at hg
  have hx : B * (B⁻¹ * splitHom σ J τ g * B) * B⁻¹ = splitHom σ J τ g := by group
  obtain ⟨c, hc⟩ := keeps_rows ε (B := B) (by rw [← hBe]; rfl) hg
  refine ⟨hx ▸ keeps_cols ε (B := B) (by rw [← hBe]) hg, ?_⟩
  rw [hx] at hc
  refine keeps_dual (G := J.map τ) (f := e'.map τ) (Units.mul_inv _) (splitGram hJ τ).mul_inv (splitHom_unitary τ g) ?_ hc
  rw [← hm]
  exact (Matrix.map_mul (f := (τ : E →+* Fv F v))).symm.trans
    (by rw [hf, Matrix.map_one _ (map_zero _) (map_one _)])

theorem iwasawa_of_triangular (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (hL : IsSelfDualAt σ J L v) (Q : Subgroup (GLoc σ J v))
    (B : GL (Fin n) (Fv F v)) (lv : Fin n → ℕ)
    (hQ : ∀ g : GLoc σ J v, (B⁻¹ * splitHom σ J τ g * B).1.BlockTriangular lv → g ∈ Q) (y : GLoc σ J v) :
    ∃ q k : GLoc σ J v, q ∈ Q ∧ k ∈ stabLoc σ J L v ∧ y = q * k := by
  obtain ⟨β, hβ⟩ : ∃ β, IsSplitBasis τ L β := exists_isSplitBasis τ L h
  have iw : ∀ x : GL (Fin n) (Fv F v), ∃ q ∈ Q, ∃ k ∈ stabLoc σ J L v,
      x * β = splitHom σ J τ q * B * β⁻¹ * splitHom σ J τ k * β := fun x => by
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    obtain ⟨b, hb, w, hw, e⟩ := GlobalTheory.SplitWeil.iwasawa_blockTriangular (Fv F v) (Fin n) lv (B⁻¹ * x * β)
    rw [← (GLint_eq_KO_and_princ_eq_KOne v n).1] at hw
    refine ⟨(splitEquivIn h hJ τ B).symm b, hQ _ ?_, (splitEquivIn h hJ τ β).symm w,
      (mem_stabLoc_iff_GLint h hJ hL hβ).2 ?_, ?_⟩
    · rwa [← splitEquivIn_apply h hJ, ContinuousMulEquiv.apply_symm_apply]
    · rwa [ContinuousMulEquiv.apply_symm_apply]
    · rw [splitHom_splitEquivIn_symm, splitHom_splitEquivIn_symm]
      calc x * β = B * (B⁻¹ * x * β) := by group
        _ = _ := by rw [e]; group
  obtain ⟨q₀, hq₀, k₀, hk₀, e₀⟩ := iw 1
  obtain ⟨q₁, hq₁, k₁, hk₁, e₁⟩ := iw (splitHom σ J τ y)
  refine ⟨q₁ * q₀⁻¹, k₀⁻¹ * k₁, mul_mem hq₁ (inv_mem hq₀), mul_mem (inv_mem hk₀) hk₁, splitHom_injective h hJ τ ?_⟩
  rw [mul_left_inj] at e₀ e₁
  rw [e₁, map_mul, map_mul, map_mul, map_inv, map_inv]
  generalize splitHom σ J τ q₀ = a₀, splitHom σ J τ q₁ = a₁, splitHom σ J τ k₀ = c₀, splitHom σ J τ k₁ = c₁ at e₀ ⊢
  rw [eq_inv_of_mul_eq_one_right e₀.symm]
  group

end Local

section Record

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem iwasawa_stab_split : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (v : FinPl D), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ y : Gv T v, ∃ q k : Gv T v, emb D.sp.cm.sig T.gram v q ∈ stab d ∧ k ∈ stabLoc D.sp.cm.sig T.gram (frameLat T) v ∧ y = q * k := by
  intro D T T₀ r d v ⟨P, P', hne, hP, hP'⟩ y
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) (v := v) hne (HeightOneSpectrum.ext hP)
    (HeightOneSpectrum.ext hP')
  haveI := SelfDual.isLattice_frameLat T
  have hf : d.qY ⬝ d.e' = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pY_jY)
  obtain ⟨B, lv, hB⟩ := exists_flag_basis τ (GlobalTheory.Doubling.isHermND_gram T) (e := d.e) (e' := d.e') (i := d.i₀)
    (p := d.qX) (q := d.q0) (Fintype.equivOfCardEq (by simp [← d.rank_add]; ring)) d.sum_eq_one_rat hf
  refine iwasawa_of_triangular (isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram T) τ (frameLat T)
    (SelfDual.isSelfDualAt_frameLat D T v) ((stab d).comap (emb D.sp.cm.sig T.gram v)) B lv (fun g hg => ?_) y
  obtain ⟨⟨a, ha⟩, a', ha'⟩ := hB g hg
  have h1 : mt T (emb D.sp.cm.sig T.gram v g) ⬝ d.jX =
      d.jX ⬝ (d.pX ⬝ (mt T (emb D.sp.cm.sig T.gram v g) ⬝ d.jX)) :=
    emb_keeps (isCMExt_host D) τ g d.pX_jX rfl ha ha'
  rw [Subgroup.mem_comap]
  generalize emb D.sp.cm.sig T.gram v g = x at h1 ⊢
  have h2 : (d.pX ⬝ (mt T x⁻¹ ⬝ d.jX)) ⬝ (d.pX ⬝ (mt T x ⬝ d.jX)) = 1 := by
    rw [Matrix.mul_assoc d.pX, Matrix.mul_assoc (mt T x⁻¹), ← h1, ← Matrix.mul_assoc (mt T x⁻¹), ← mt_mul,
      inv_mul_cancel, mt_one, Matrix.one_mul, d.pX_jX]
  exact ⟨⟨_, _, mul_eq_one_comm.1 h2, h2⟩, h1⟩

end Record

end GlobalTheory.Core.Rk.IwFlagSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevChiWithPOfMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.LevelWithP

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levelCharacter_withLevel_of_mem {P : LevelP L.Pg L.r ℂ} {κ : GA D V} (hp : rTup β L (Lev.finE V κ) ∈ P.H) :
    Lev.levChi V β (Lev.withP L P) κ = ((P.chi ⟨_, hp⟩ : ℂˣ) : ℂ) * Lev.levChi V β (Lev.flagL L) κ := by
  unfold Lev.levChi
  rw [Lev.levFn_withP, extendOne_of_mem _ hp, Units.val_mul]

theorem hasType_withCharacter_iff (P : LevelP L.Pg L.r ℂ) (F : GA D V → ℂ) :
    Lev.HasType V β (Lev.withP L P) F ↔ Lev.HasType V β (Lev.flag1L L) F ∧
      ∀ (p : P.H) κ, Lev.IsLevelLift V β L p.1 κ → ∀ g,
        (Lev.levChi V β (Lev.flagL L) κ)⁻¹ * F (g * κ) = ((P.chi p : ℂˣ) : ℂ) * F g := by
  constructor
  · intro h
    refine ⟨fun κ hκ g => ?_, fun p κ hκ g => ?_⟩
    · have h1 : rTup β L (Lev.finE V κ) = 1 := Subgroup.mem_bot.1 hκ.2.2
      have hp : rTup β L (Lev.finE V κ) ∈ P.H := by rw [h1]; exact P.H.one_mem
      have hw : κ ∈ Lev.levG V β (Lev.withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
      rw [h κ hw g]
      congr 1
      rw [levelCharacter_withLevel_of_mem hp]
      have e : (⟨_, hp⟩ : P.H) = 1 := Subtype.ext h1
      rw [e, map_one, Units.val_one, one_mul]
      unfold Lev.levChi
      rw [Lev.levFn_flag1]
    · have hp : rTup β L (Lev.finE V κ) ∈ P.H := by rw [hκ.2.2]; exact p.2
      have hw : κ ∈ Lev.levG V β (Lev.withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
      have hne := Lev.levChi_ne_zero (β := β) (Lev.flagL L) κ
      rw [h κ hw g, levelCharacter_withLevel_of_mem hp]
      have e : (⟨_, hp⟩ : P.H) = p := Subtype.ext hκ.2.2
      rw [e, inv_mul_eq_iff_eq_mul₀ hne]
      ring
  · rintro ⟨-, h⟩ κ hκ g
    have hp : rTup β L (Lev.finE V κ) ∈ P.H := hκ.2.2
    have hl : Lev.IsLevelLift V β L (⟨_, hp⟩ : P.H).1 κ := ⟨hκ.1, hκ.2.1, rfl⟩
    have key := h ⟨_, hp⟩ κ hl g
    have hne := Lev.levChi_ne_zero (β := β) (Lev.flagL L) κ
    rw [inv_mul_eq_iff_eq_mul₀ hne] at key
    rw [key, levelCharacter_withLevel_of_mem hp]
    ring

end GlobalTheory.ChainOnto.LevelWithP


open GlobalTheory.ChainOnto.LevelWithP in
theorem GlobalTheory.ChainOnto.LevelWithP.mem_multT_withP_iff : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P : LevelP L.Pg L.r ℂ) (T : SmT M →ₗ[ℂ] (GA D V → ℂ)), T ∈ MultT θ M (levS V β (Lev.withP L P)) (Lev.levChi V β (Lev.withP L P)) ↔ T ∈ MultT θ M (levS V β (Lev.flag1L L)) (Lev.levChi V β (Lev.flag1L L)) ∧ ∀ (p : P.H) κ, Lev.IsLevelLift V β L p.1 κ → ∀ w g, (Lev.levChi V β (Lev.flagL L) κ)⁻¹ * T w (g * κ) = ((P.chi p : ℂˣ) : ℂ) * T w g := by
  intro D θ V S M β L P T
  rw [mem_multT, mem_multT, GlobalTheory.MultMem.mem_mult_iff, GlobalTheory.MultMem.mem_mult_iff]
  constructor
  · intro h
    have hT : ∀ v, Lev.HasType V β (Lev.withP L P) (PiTensorProduct.lift.symm T v) := fun v κ hκ g => h.lev v κ hκ g
    refine ⟨⟨h.aut, h.cusp, fun v κ hκ g => ((hasType_withCharacter_iff P _).1 (hT v)).1 κ hκ g, h.equiv, h.cont⟩, ?_⟩
    intro p κ hκ w g
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have key : (Lev.levChi V β (Lev.flagL L) κ)⁻¹ * T (PiTensorProduct.tprod ℂ v) (g * κ) =
          ((P.chi p : ℂˣ) : ℂ) * T (PiTensorProduct.tprod ℂ v) g := ((hasType_withCharacter_iff P _).1 (hT v)).2 p κ hκ g
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      linear_combination r * key
    | add x y hx hy =>
      simp only [map_add (f := _), Pi.add_apply]
      linear_combination hx + hy
  · rintro ⟨h, hP⟩
    refine ⟨h.aut, h.cusp, fun v κ hκ g => ?_, h.equiv, h.cont⟩
    refine (hasType_withCharacter_iff P _).2 ⟨fun κ hκ g => h.lev v κ hκ g, fun p κ' hκ' g' => ?_⟩ κ hκ g
    exact hP p κ' hκ' _ g'

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelMeasurePushforwardEqProductRealMeasures
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RealBoxMeasure

variable {D : D7}

theorem exists_realPart (θ : InfFam D) (hθ : IsInfFam θ) (W : HSp D) (hW : W.SigOK) (Fr : Frames W)
    (hFr : IsFrames W Fr) :
    ∃ φ : GA D W → ∀ ρ, Upq W ρ, Continuous φ ∧
      ∀ h ρ, UpqT.mat (φ h ρ) * Fr ρ = Fr ρ * infMat D.sp.cm.sig W.gram (θ ρ) h := by
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  obtain ⟨e1, he1⟩ := GlobalTheory.Mem.InfGroup.real_points D.host.F D.host.E D.sp.cm.sig W.rank W.gram D.what₂.Tau (tauE D) θ
    (fun ρ => (W.sig (tauE D ρ)).1) (fun ρ => (W.sig (tauE D ρ)).2) Fr hcm hτ hθ (fun i => hW (tauE D i)) hFr
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig W.rank W.gram
  refine ⟨fun h => e1 (e0 h).1, e1.continuous.comp (continuous_fst.comp e0.continuous), fun h i => ?_⟩
  show UpqT.mat (e1 (e0 h).1 i) * Fr i = _
  rw [he1, (he0 h).2]; rfl

theorem mat_cancel (W : HSp D) (hW : W.SigOK) (Fr : Frames W) (hFr : IsFrames W Fr) (ρ : D.what₂.Tau)
    {b b' : Upq W ρ} (h : UpqT.mat b * Fr ρ = UpqT.mat b' * Fr ρ) : b = b' := by
  obtain ⟨C, h1, -⟩ := (GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (tauE D ρ))).2.2 (Fr ρ) (hFr ρ)
  apply (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.2.injective
  have h5 := congrArg (· * C) h
  simpa only [Matrix.mul_assoc, h1, Matrix.mul_one] using h5

theorem realMat_of (W : HSp D) (Fr : Frames W) (hFr : IsFrames W Fr) (ρ : D.what₂.Tau) (b : Upq W ρ)
    (M : Matrix (Fin W.rank) (Fin W.rank) ℂ) (h : UpqT.mat b * Fr ρ = Fr ρ * M) : realMat W Fr ρ b = M := by
  have hG := GlobalTheory.SmoothForms.RealPts.gramAt_unit W ρ
  unfold realMat conjFrame
  have e : (Fr ρ)ᴴ * Formalism.UG.Jpq (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 * (Fr ρ * M) = gramAt D W ρ * M := by
    rw [← Matrix.mul_assoc, hFr ρ]
  rw [Matrix.mul_assoc (_ * _), h, e, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]

theorem realMat_mem (W : HSp D) (hW : W.SigOK) (Fr : Frames W) (hFr : IsFrames W Fr) (ρ : D.what₂.Tau) (b : Upq W ρ) :
    realMat W Fr ρ b ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ) :=
  conjFrame_mem_UH _ _ _ (GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (tauE D ρ))).1 _ _ (hFr ρ)
    (GlobalTheory.SmoothForms.RealPts.gramAt_unit W ρ) b

theorem infMat_realElt (θ : InfFam D) (hθ : IsInfFam θ) (W : HSp D) (u : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hu : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ)) (ρ : D.what₂.Tau) :
    infMat D.sp.cm.sig W.gram (θ ρ) (realElt θ W u) = u ρ := by
  rw [realElt, GlobalTheory.RealTransSm.infMat_list_prod hθ u hu ρ _ (Finset.nodup_toList _),
    if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ))]

theorem realElt_mem (θ : InfFam D) (W : HSp D) (u : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    realElt θ W u ∈ GinfC W := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
  exact GlobalTheory.PointAtPlaceHom.atTau_mem W τ (u τ)

theorem finE_realElt (θ : InfFam D) (W : HSp D) (u : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    finE W (realElt θ W u) = 1 := by
  rw [Lev.finE_eq, (MonoidHom.mem_ker).1 (realElt_mem θ W u), map_one]

theorem continuous_realElt (θ : InfFam D) (hθ : IsInfFam θ) (W : HSp D) (hW : W.SigOK) (Fr : Frames W)
    (hFr : IsFrames W Fr) :
    Continuous fun b : (∀ ρ, Upq W ρ) => realElt θ W fun ρ => realMat W Fr ρ (b ρ) := by
  haveI : IsTopologicalGroup (GA D W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  unfold realElt
  refine continuous_list_prod _ fun ρ _ => ?_
  have hκ : Continuous fun b : (∀ ρ, Upq W ρ) => realMat W Fr ρ (b ρ) := by
    unfold realMat conjFrame
    exact continuous_const.matrix_mul (((continuous_const.matrix_mul
      ((GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.2.continuous.comp (continuous_apply ρ))).matrix_mul continuous_const))
  exact (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ W ρ).comp_continuous hκ
    fun b => realMat_mem W hW Fr hFr ρ (b ρ)

theorem lintegral_levelSet_eq_pi : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D), W.SigOK → ∀ (K : Subgroup (GL (Fin W.rank) (Lev.EAf D))) (ν : Measure (GA D W)), IsMeasLev W K ν → ∀ Fr : Frames W, IsFrames W Fr → ∀ mR : ∀ ρ, Measure (Upq W ρ), (∀ ρ, Lev.IsMinf (mR ρ)) → ∀ Z : GA D W → ENNReal, Measurable Z → (∀ g, ∀ k ∈ levA W K, Z (g * k) = Z g) → MeasurableSet {h : GA D W | finE W h ∈ K} → ∫⁻ g in {h : GA D W | finE W h ∈ K}, Z g ∂ν = ∫⁻ b, Z (realElt θ W fun ρ => realMat W Fr ρ (b ρ)) ∂(Measure.pi mR) := by
  intro D θ hθ W hW K ν hν Fr hFr mR hmR Z hZ hZK hS
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, hsc, hbo, -⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable W
  haveI := hsc
  haveI := hbo
  haveI : ∀ ρ, SigmaFinite (mR ρ) := fun ρ => by haveI := (hmR ρ).1; infer_instance
  obtain ⟨φ, hφc, hφ⟩ := exists_realPart θ hθ W hW Fr hFr
  have hφm : Measurable φ := hφc.measurable
  set sec : (∀ ρ, Upq W ρ) → GA D W := fun b => realElt θ W fun ρ => realMat W Fr ρ (b ρ) with hsec
  have hsecm : Measurable (fun b => Z (sec b)) := hZ.comp (continuous_realElt θ hθ W hW Fr hFr).measurable
  obtain ⟨-, -, H⟩ := hν
  obtain ⟨-, H1⟩ := H θ hθ
  obtain ⟨-, H2⟩ := H1 Fr hFr
  have hpi : Measure.pi mR = Measure.map φ (ν.restrict {h : GA D W | finE W h ∈ K}) := by
    refine Measure.pi_eq fun B hB => ?_
    have hm : MeasurableSet (φ ⁻¹' Set.univ.pi B) := hφm (MeasurableSet.univ_pi hB)
    rw [Measure.map_apply hφm (MeasurableSet.univ_pi hB), Measure.restrict_apply hm, ← H2 mR hmR B hB]
    congr 1
    ext h
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq]
    rw [and_comm]
    refine and_congr_right fun _ => forall_congr' fun ρ => ⟨fun hb => ⟨φ h ρ, hb, hφ h ρ⟩, ?_⟩
    rintro ⟨b, hb, hbe⟩
    rwa [mat_cancel W hW Fr hFr ρ (hbe.trans (hφ h ρ).symm)] at hb
  have hfac : ∀ h ∈ {h : GA D W | finE W h ∈ K}, Z h = Z (sec (φ h)) := by
    intro h hh
    have e : ∀ ρ, infMat D.sp.cm.sig W.gram (θ ρ) (sec (φ h)) = infMat D.sp.cm.sig W.gram (θ ρ) h := fun ρ => by
      rw [hsec]
      dsimp only
      rw [infMat_realElt θ hθ W _ (fun τ => realMat_mem W hW Fr hFr τ _) ρ]
      exact realMat_of W Fr hFr ρ _ _ (hφ h ρ)
    have hk : (sec (φ h))⁻¹ * h ∈ levA W K := by
      refine ⟨(GlobalTheory.SmoothForms.RealPts.glue θ hθ W).1 _ fun ρ => ?_, ?_⟩
      · rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← e ρ, ← GlobalTheory.PointAtPlaceHom.infMat_mul, inv_mul_cancel,
          GlobalTheory.PointAtPlaceHom.infMat_one]
      · show finE W ((sec (φ h))⁻¹ * h) ∈ K
        rw [map_mul, map_inv, hsec]
        dsimp only
        rw [finE_realElt, inv_one, one_mul]
        exact hh
    rw [← hZK (sec (φ h)) _ hk, mul_inv_cancel_left]
  calc ∫⁻ g in {h : GA D W | finE W h ∈ K}, Z g ∂ν
      = ∫⁻ g in {h : GA D W | finE W h ∈ K}, Z (sec (φ g)) ∂ν := setLIntegral_congr_fun hS hfac
    _ = ∫⁻ b, Z (sec b) ∂(Measure.map φ (ν.restrict {h : GA D W | finE W h ∈ K})) :=
        (lintegral_map hsecm hφm).symm
    _ = _ := by rw [← hpi]

end GlobalTheory.RealBoxMeasure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHyperspecialSubgroupAtPlaceIffLocalStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

noncomputable section

namespace GlobalTheory.HypDict

theorem mem_hyp_iff_embV : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → ∀ (V : HSp D) (g : GA D V), g ∈ GlobalTheory.Hk3.hyp V w ↔ ∃ k ∈ Kv V v, g = embV V v k := by
  intro D v w hw V g
  obtain ⟨e, f, hP⟩ := (_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.1 w
  rw [GlobalTheory.LevOp.mem_hyp hP, GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem V hP hw g, GlobalTheory.AdelicU.KsphC_eq]
  constructor
  · rintro ⟨hk, k, rfl⟩
    refine ⟨k, ?_, rfl⟩
    have := (GlobalTheory.AdelicU.mem_levelOff.1 hk).2.2 v (Finset.notMem_empty v)
    simpa using this
  · rintro ⟨k, hk, rfl⟩
    exact ⟨GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk, k, rfl⟩

end GlobalTheory.HypDict

end
end

