module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClTwistEqSelfOfEqOne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory

open GlobalTheory.SmGL GlobalTheory.LocGL in
private theorem clTwist_eq_self_of_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (c : IrrCl G) (χ : G →* ℂˣ) (hχ : IsSmoothChar χ) (h1 : χ = 1) : clTwist c χ hχ = c := by
  subst h1; exact clTwist_one c hχ

theorem rankOne_algNorm_locComp (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (π : CuspSub E 1)
    (ψ : HChar E) (hπ : CG.mk π = CG.ofChar ψ) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin 1) (w.adicCompletion E))) (hσ : π.IsLocComp w σ) :
    algNorm σ = IrrGL.ofChar (ψ.loc w) (ParLaws.isSmoothChar_loc ψ w) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [hπ] at h1
  have h2 := CG.IsLoc.unique E 1 _ w _ _ h1 (CG.isLoc_ofChar ψ w)
  obtain ⟨e⟩ := Quotient.exact h2
  unfold algNorm IrrGL.nu IrrGL.tw IrrGL.of IrrGL.ofChar
  congr 1
  refine (clTwist_eq_self_of_eq_one _ _ _ ?_).trans ?_
  · ext g
    simp [GlobalTheory.SmGL.detChar, GlobalTheory.SmGL.absPow]
  apply Quotient.sound
  exact ⟨e.trans (Representation.Equiv.refl _)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecompose
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open TensorProduct

namespace GlobalTheory.IdemSplit

variable {R : Type*} [CommRing R] {n : ℕ}

def fold (e : R) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := e • M + (1 - e) • 1

theorem fold_mul_fold {e : R} (he : e * e = e) (X Y : Matrix (Fin n) (Fin n) R) :
    fold e X * fold (1 - e) Y = e • X + (1 - e) • Y := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, h0, sub_zero]
  simp only [fold, sub_sub_cancel, add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, h0, h0',
    he, h1, zero_smul, zero_add, add_zero]
  exact add_comm _ _

theorem fold_mul_fold' {e : R} (he : e * e = e) (X Y : Matrix (Fin n) (Fin n) R) :
    fold (1 - e) Y * fold e X = e • X + (1 - e) • Y := by
  have he' : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have h := fold_mul_fold he' Y X
  rw [sub_sub_cancel] at h
  rw [h, add_comm]

theorem fold_mul {e : R} (he : e * e = e) (X Y : Matrix (Fin n) (Fin n) R) :
    fold e X * fold e Y = fold e (X * Y) := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, h0, sub_zero]
  simp only [fold, add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, h0, h0',
    he, h1, zero_smul, zero_add, add_zero]

theorem fold_one (e : R) : fold e (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [fold, ← add_smul, add_sub_cancel, one_smul]

theorem conjT_fold (σ : R →+* R) {e : R} (hσ : σ e = e) (M : Matrix (Fin n) (Fin n) R) :
    conjT σ (fold e M) = fold e (conjT σ M) := by
  ext i j
  simp only [conjT, fold, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hσ, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

def unitsFold {e : R} (he : e * e = e) (g : GL (Fin n) R) : GL (Fin n) R :=
  ⟨fold e g, fold e (g⁻¹ : GL (Fin n) R), by rw [fold_mul he, Units.mul_inv, fold_one],
    by rw [fold_mul he, Units.inv_mul, fold_one]⟩

theorem unitsFold_mem_UGroup (σ : R →+* R) (hσ2 : ∀ x, σ (σ x) = x) {e : R} (he : e * e = e)
    (hσ : σ e = e) (g : GL (Fin n) R) (hg : g ∈ UGroup n σ hσ2) :
    unitsFold he g ∈ UGroup n σ hσ2 := by
  have hg' : (g : Matrix (Fin n) (Fin n) R) * conjT σ g = 1 := hg
  show fold e (g : Matrix (Fin n) (Fin n) R) * conjT σ (fold e (g : Matrix (Fin n) (Fin n) R)) = 1
  rw [conjT_fold σ hσ, fold_mul he, hg', fold_one]

theorem fold_apply (e : R) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    fold e M i j = e * M i j + (1 - e) * (1 : Matrix (Fin n) (Fin n) R) i j := by
  simp [fold]

end GlobalTheory.IdemSplit

namespace GlobalTheory.CongSplit

open GlobalTheory.IdemSplit GlobalTheory.InertUmax

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

def idemAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L :=
  (1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1

theorem compAt_idemAt_self (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    compAt L v (idemAt L v) = 1 := by
  rw [idemAt, compAt_tmul, sgl_same]; rfl

theorem compAt_idemAt_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hw : w ≠ v) :
    compAt L w (idemAt L v) = 0 := by
  rw [idemAt, compAt_tmul, sgl_ne L v 1 hw, tmul_zero]

theorem idemAt_mul_self (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    idemAt L v * idemAt L v = idemAt L v := by
  apply sub_eq_zero.1
  apply eq_zero_of_compAt
  intro w
  rw [map_sub, map_mul]
  rcases eq_or_ne w v with rfl | hw
  · rw [compAt_idemAt_self, mul_one, sub_self]
  · rw [compAt_idemAt_ne L v hw, mul_zero, sub_self]

theorem idemAt_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : idemAt L v ∈ ALint L :=
  one_tmul_sgl_mem L v 1 (one_mem _)

theorem conjAL_idemAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    conjAL L (idemAt L v) = idemAt L v := by
  simp [conjAL, idemAt, Algebra.TensorProduct.map_tmul]

theorem one_apply_mem {n : ℕ} (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem compAt_one_apply {n : ℕ} (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (i j : Fin n) :
    compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
  simp only [Matrix.one_apply]
  split_ifs <;> simp


variable {L} in
def gaFold {n : ℕ} {f : AL L} (hf : f * f = f) (hσ : conjAL L f = f) (g : GAf L n) : GAf L n :=
  ⟨unitsFold hf g.1, unitsFold_mem_UGroup (conjAL L) (conjAL_conjAL L) hf hσ g.1 g.2⟩

theorem gaFold_val {n : ℕ} {f : AL L} (hf : f * f = f) (hσ : conjAL L f = f) (g : GAf L n) :
    ((gaFold hf hσ g).1 : Matrix (Fin n) (Fin n) (AL L)) = fold f (g.1 : Matrix (Fin n) (Fin n) (AL L)) :=
  rfl

theorem gaFold_mem_Umax {n : ℕ} {f : AL L} (hf : f * f = f) (hσ : conjAL L f = f) (hfi : f ∈ ALint L)
    (g : GAf L n) (hg : g ∈ Umax L n) : gaFold hf hσ g ∈ Umax L n := by
  intro i j
  rw [gaFold_val, fold_apply]
  exact Subring.add_mem _ (Subring.mul_mem _ hfi (hg i j))
    (Subring.mul_mem _ (Subring.sub_mem _ (one_mem _) hfi) (one_apply_mem L i j))

theorem decomp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ) (c : GAf L n), NG.Cong L n N c → ∃ a b : GAf L n, c = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x := by
  intro L _ _ _ n v N c hc
  set e := idemAt L v with he_def
  have he : e * e = e := idemAt_mul_self L v
  have he' : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have hσ : conjAL L e = e := conjAL_idemAt L v
  have hσ' : conjAL L (1 - e) = 1 - e := by rw [map_sub, map_one, hσ]
  have hei : e ∈ ALint L := idemAt_mem L v
  have hei' : 1 - e ∈ ALint L := Subring.sub_mem _ (one_mem _) hei
  refine ⟨gaFold he hσ c, gaFold he' hσ' c, ?_, gaFold_mem_Umax L he hσ hei c hc.1, ?_, ?_, ?_⟩
  · apply Subtype.ext; apply Units.ext
    show (c.1 : Matrix (Fin n) (Fin n) (AL L)) = fold e _ * fold (1 - e) _
    rw [fold_mul_fold he, ← add_smul, add_sub_cancel, one_smul]
  · intro w hw
    have hw' : w ≠ v := by simpa using hw
    ext i j
    rw [Matrix.map_apply, gaFold_val, fold_apply, map_add (f := _), map_mul, map_mul, map_sub, map_one,
      compAt_idemAt_ne L v hw', compAt_one_apply]
    simp
  · refine ⟨gaFold_mem_Umax L he' hσ' hei' c hc.1, fun i j => ?_⟩
    obtain ⟨y, hy, hEq⟩ := hc.2 i j
    refine ⟨(1 - e) * y, Subring.mul_mem _ hei' hy, ?_⟩
    rw [gaFold_val, fold_apply, sub_sub_cancel]
    linear_combination (1 - e) * hEq
  · intro x hx
    have hxf : (x.1 : Matrix (Fin n) (Fin n) (AL L)) = fold e (x.1 : Matrix (Fin n) (Fin n) (AL L)) := by
      ext i j
      apply sub_eq_zero.1
      rw [fold_apply]
      apply eq_zero_of_compAt
      intro w
      rcases eq_or_ne w v with rfl | hw
      · rw [map_sub, map_add (f := _), map_mul, map_mul, map_sub, map_one, compAt_idemAt_self]
        ring
      · have h := congrFun (congrFun (hx w (by simpa using hw)) i) j
        rw [Matrix.map_apply] at h
        rw [map_sub, map_add (f := _), map_mul, map_mul, map_sub, map_one, compAt_idemAt_ne L v hw,
          compAt_one_apply, h]
        ring
    apply Subtype.ext; apply Units.ext
    show (x.1 : Matrix (Fin n) (Fin n) (AL L)) * fold (1 - e) _ = fold (1 - e) _ * (x.1 : Matrix (Fin n) (Fin n) (AL L))
    rw [hxf, fold_mul_fold he, fold_mul_fold' he]

end GlobalTheory.CongSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TypeTame

theorem conjSP_w_of_isConjPl : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), IsConjPl D.host w s.w → (GlobalTheory.TypeTame.conjSP s).w = w ∧ ∀ x : D.host.E, (GlobalTheory.TypeTame.conjSP s).i x = s.i (D.host.conj x) := by
  intro D s w hw
  have hc : ∀ z : D.host.E, IsCMField.complexConj D.host.E z = D.host.conj z := by
    intro z
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  refine ⟨?_, fun x => by rw [conjSP_i, hc]⟩
  let c : 𝓞 D.host.E →+* 𝓞 D.host.E :=
    RingOfIntegers.mapRingHom (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E)
  have hce : ∀ e : 𝓞 D.host.E, ((c e : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (e : D.host.E) :=
    fun e => rfl
  ext x
  have h1 : x ∈ (conjSP s).w.asIdeal ↔ c x ∈ s.w.asIdeal := by
    show Valued.v ((conjSP s).i (x : D.host.E)) < 1 ↔ Valued.v (s.i ((c x : 𝓞 D.host.E) : D.host.E)) < 1
    rw [conjSP_i, hce]
  rw [h1, hw x (c x) (by rw [hce, hc])]

end GlobalTheory.TypeTame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceUnitaryLocEqTransposeInv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open TensorProduct

namespace GlobalTheory.ConjLoc

theorem proj_conjSP {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (a : AL L) :
    (GlobalTheory.TypeTame.conjSP s).proj a = s.proj (conjAL L a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x b =>
    simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem loc_conjSP : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (x : GAf L n), ((GlobalTheory.TypeTame.conjSP s).loc n x).val = ((s.loc n x)⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose := by
  intro L _ _ _ n s x
  have hx : (x.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have h1 : (s.loc n x).val * ((GlobalTheory.TypeTame.conjSP s).loc n x).val.transpose = 1 := by
    have e : ((GlobalTheory.TypeTame.conjSP s).loc n x).val.transpose
        = (conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L))).map s.proj := by
      refine Matrix.ext fun i j => ?_
      exact proj_conjSP s _
    have e' : (s.loc n x).val = (x.1 : Matrix (Fin n) (Fin n) (AL L)).map s.proj := rfl
    rw [e, e', ← Matrix.map_mul, hx, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 := Units.inv_eq_of_mul_eq_one_right h1
  rw [h2, Matrix.transpose_transpose]

end GlobalTheory.ConjLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineDecompositionGroupNoMonodromy
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open _root_.GlobalTheory GlobalTheory.Cong GlobalTheory.UnitaryBC

namespace GlobalTheory.CrysNoMono

theorem crystalline_decompositionGroup_no_monodromy : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (P : LocPrime l) (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω)
    (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) (ρ : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)),
    IsCrysAt P Bw ρ → (GlobalTheory.Pst.wdAt P ι Bw h hj ρ).mono0 := by
  intro E Ω _ _ _ _ _ l _ ι a P w A h O _ _ _ Bw hj ρ hc
  by_cases hr : IsPstAt P Bw ρ
  · exact (GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj P ι ρ hr).2 hc.isPotCrysAt
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, trivWD]
    exact WD.unr_mono0 _ ((WD.unr_mk _).2 (WDRep.unr_diag _))

end GlobalTheory.CrysNoMono
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamAndJumpsRankOneLAdicCharacter
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.TripleGal GlobalTheory.Pst
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CharAboveRead

open scoped TensorProduct

theorem exists_isInduced_of {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (τ : E →+* Om l) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l)
    (hτ : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) (A : ValuationSubring Ω) (hA : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
    (hj : Induces Bw) : ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1, IsInduced Bw τ τ' := by
  let jE : E →+* Om l := Bw.j.comp (algebraMap E Ω)
  have hjE : ∀ x : 𝓞 E, ‖jE (x : E)‖ < 1 ↔ x ∈ w.asIdeal := fun x =>
    (hj.valuation_lt_one_iff _).symm.trans (hA x)
  have iso := GlobalTheory.GalFirstClause.Emb.norm_eq_of_samePlace τ jE w hw hτ hjE
  have hker : ∀ t ∈ RingHom.ker (GlobalTheory.GalFirstClause.Emb.tensLift jE), GlobalTheory.GalFirstClause.Emb.tensLift τ t = 0 := fun t ht =>
    norm_eq_zero.1 (le_antisymm ((GlobalTheory.GalFirstClause.Emb.norm_tensLift_le jE τ (fun x => (iso x).symm) t).trans
      (by rw [RingHom.mem_ker.1 ht, norm_zero])) (norm_nonneg _))
  have hrange : (GlobalTheory.GalFirstClause.Emb.tensLift jE).range ≤ Bw.Kw.1.toSubalgebra := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a y =>
      change GlobalTheory.GalFirstClause.Emb.tensLift jE (a ⊗ₜ y) ∈ _
      rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul]
      exact mul_mem (Bw.Kw.1.algebraMap_mem a) (Bw.j_E y)
    | add t₁ t₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  have hfin : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule (GlobalTheory.GalFirstClause.Emb.tensLift jE).range) := by
    haveI : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra) := Bw.Kw.2
    exact Submodule.finiteDimensional_of_le (Subalgebra.toSubmodule.monotone hrange)
  have hclosed : IsClosed ((GlobalTheory.GalFirstClause.Emb.tensLift jE).range : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule (GlobalTheory.GalFirstClause.Emb.tensLift jE).range)
  have hle : Bw.Kw.1.toSubalgebra ≤ (GlobalTheory.GalFirstClause.Emb.tensLift jE).range := by
    intro y hy
    refine closure_minimal ?_ hclosed (Bw.j_dense hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by
      change GlobalTheory.GalFirstClause.Emb.tensLift jE (1 ⊗ₜ x) = jE x; rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]⟩
  let σ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l :=
    ((Ideal.Quotient.liftₐ (RingHom.ker (GlobalTheory.GalFirstClause.Emb.tensLift jE)) (GlobalTheory.GalFirstClause.Emb.tensLift τ) hker).comp
      (Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm.toAlgHom).comp (Subalgebra.inclusion hle)
  refine ⟨σ.codRestrict Bw.LL.1.toSubalgebra (fun y => Bw.LL_split σ y), fun x => ?_⟩
  have key : (Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm
      (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩) = Ideal.Quotient.mk _ (1 ⊗ₜ x) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    change jE x = GlobalTheory.GalFirstClause.Emb.tensLift jE (1 ⊗ₜ x)
    rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]
  change τ x = σ ⟨jE x, Bw.j_E x⟩
  change τ x = Ideal.Quotient.liftₐ _ (GlobalTheory.GalFirstClause.Emb.tensLift τ) hker
    ((Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩))
  rw [key, Ideal.Quotient.liftₐ_apply]
  change τ x = GlobalTheory.GalFirstClause.Emb.tensLift τ (1 ⊗ₜ x)
  rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]

theorem continuous_rankOneOperator {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (μ : Γ →* Kˣ) (hμ : Continuous μ) : Continuous fun g => ((rk1 μ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) := by
  have hv : Continuous fun g => ((μ g : Kˣ) : K) := Units.continuous_val.comp hμ
  refine continuous_pi fun i => continuous_pi fun k => ?_
  have e : ∀ g, ((rk1 μ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) i k = ((μ g : Kˣ) : K) := fun g => by
    fin_cases i; fin_cases k; simp [rk1]
  simp only [e]
  exact hv

end GlobalTheory.CharAboveRead

namespace GlobalTheory.CharAboveRead


set_option maxHeartbeats 1000000 in
theorem deRham_and_jumps_rankOne_lAdic_character : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (μ : G D.host.E D.nd.Om →* (Qbar l)ˣ), Continuous μ → ∀ (J : (D.host.E →+* Qbar l) → Multiset ℤ)
    (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l →
    (∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), Induces Bw →
      IsdRAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) ∧
      ∀ (τ : D.host.E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ (J τ)) →
    W.IsdRW l ι (rk1 μ) w ∧ ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) →
      W.jumpsW l ι (rk1 μ) τ = J τ := by
  intro D T W l _ ι μ hμ J w hw H
  have hcont : Continuous fun g => (rk1 μ g : Matrix (Fin 1) (Fin 1) (Qbar l)) := continuous_rankOneOperator μ hμ
  obtain ⟨K, ρ, hρc, hρ⟩ := GlobalTheory.GalFirstClause.finextRep l D.host.E D.nd.Om 1 (rk1 μ) hcont
  obtain ⟨j, L0, hj, hLL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l D.host.E D.nd.Om w (D.nd.plOm.1 w) hw (D.nd.plOm.2 w)
  obtain ⟨Bw, hBj, hBLL, -, hBto⟩ := hLL L0 le_rfl
  have hind : Induces Bw := fun x => by rw [hBj]; exact hj x
  let LL' : FinExt l := supExt K Bw.LL
  have hK : K.1 ≤ LL'.1 := le_sup_left
  have hB : Bw.LL.1 ≤ LL'.1 := le_sup_right
  let ρ' : G D.host.E D.nd.Om →* GL (Fin 1) ↥LL'.1 := mapRep (IntermediateField.inclusion hK).toRingHom ρ
  have hρ' : mapRep (algebraMap ↥LL'.1 (Om l)) ρ' = rk1 μ := by
    rw [← hρ]
    ext g i k
    rfl
  have hρ'c : Continuous fun g => (ρ' g : Matrix (Fin 1) (Fin 1) ↥LL'.1) := by
    have hi : Continuous (IntermediateField.inclusion hK) :=
      continuous_induced_rng.2 continuous_subtype_val
    exact hρc.matrix_map hi
  have hmodel : IsModel Bw (resDec D.nd.plOm.1 (rk1 μ) w) LL'
      (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    ⟨hB, by rw [← hρ']; rfl⟩
  let φ : ↥(OL L0) →+* Qbar l := L0.1.val.toRingHom.comp (OL L0).val.toRingHom
  have hφ : ∀ x, φ x = ((Bw.toLL x : ↥Bw.LL.1) : Om l) := fun x => (hBto x).symm
  have hcl := (W.loc l ι w hw _ Bw hind φ hφ).2 LL' hB 1 ρ' hρ'c
  rw [hρ'] at hcl
  have hab := H _ Bw hind
  have hdR : Bw.IsdRE (D.loc l) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    (hmodel.isdRAt_iff (D.loc l)).1 hab.1
  refine ⟨hcl.2.1.2 hdR, fun τ hτ => ?_⟩
  obtain ⟨τ₀, hτ₀⟩ := exists_isInduced_of τ w hw hτ _ (D.nd.plOm.2 w) _ Bw hind
  let τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1 := (IntermediateField.inclusion hB).comp τ₀
  have hτ'' : IsInduced Bw τ τ'' := fun x => hτ₀ x
  have hJ := hab.2 τ LL' τ'' hτ''
  ext n
  apply Nat.cast_injective (R := ℤ)
  rw [(hcl.2.2.2 τ τ'' hτ'').2 hdR n, IsJumpsAt.count_eq (D.loc l) hmodel hτ'' hJ n]

end GlobalTheory.CharAboveRead
end
end

