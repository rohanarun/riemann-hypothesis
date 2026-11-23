module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0427
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTameInflationCharacterOfPadicIso
section
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys ValuativeRel Filter Topology

namespace GlobalTheory.TameRead

theorem toZMod_surj (g : ℕ) [Fact g.Prime] : Function.Surjective (PadicInt.toZMod (p := g)) := by
  intro a
  refine ⟨(a.val : ℤ_[g]), ?_⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem units_toZMod_surj (g : ℕ) [Fact g.Prime] :
    Function.Surjective (Units.map (PadicInt.toZMod (p := g)).toMonoidHom) := by
  have : IsLocalHom (PadicInt.toZMod (p := g)) := IsLocalHom.of_surjective _ (toZMod_surj g)
  exact IsLocalRing.surjective_units_map_of_local_ringHom _ (toZMod_surj g) this

theorem val_sub_one_lt (g : ℕ) [Fact g.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F) (he : Continuous e) (u : ℤ_[g])
    (hu : PadicInt.toZMod u = 1) : valuation F (e (u : ℚ_[g]) - 1) < 1 := by
  have hm : u - 1 ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, hu, map_one, sub_self]
  have hn : ‖u - 1‖ < 1 := PadicInt.mem_nonunits.1 hm
  have hn' : ‖((u : ℚ_[g]) - 1)‖ < 1 := by
    have : ((u - 1 : ℤ_[g]) : ℚ_[g]) = (u : ℚ_[g]) - 1 := by push_cast; rfl
    rw [← this]; exact hn
  have ht : Tendsto (fun n : ℕ => ((u : ℚ_[g]) - 1) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn'
  have ht' : Tendsto (fun n : ℕ => (e ((u : ℚ_[g]) - 1)) ^ n) atTop (𝓝 0) := by
    have := (he.tendsto 0).comp ht
    simpa [Function.comp_def, map_pow] using this
  have h1 : e ((u : ℚ_[g]) - 1) = e (u : ℚ_[g]) - 1 := by rw [map_sub, map_one]
  rw [← h1]
  exact (GlobalTheory.FlatFBCompare.val_lt_one_iff _).2 ht'

theorem exists_tamePart : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ ξ : Fˣ →* ℂˣ, GlobalTheory.SplitWeil.IsTame ξ →
    ∃ χ : (ZMod g)ˣ →* ℂˣ, TamePart (ξ.comp (Units.map e.toMonoidHom)) χ := by
  intro g _ F _ _ _ _ e he ξ hξ
  let μ : ℤ_[g]ˣ →* ℂˣ := (ξ.comp (Units.map e.toMonoidHom)).comp (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom)
  have hker : (Units.map (PadicInt.toZMod (p := g)).toMonoidHom).ker ≤ μ.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have hu' : PadicInt.toZMod (u : ℤ_[g]) = 1 := by
      have := congrArg (fun x : (ZMod g)ˣ => (x : ZMod g)) hu
      simpa using this
    apply hξ
    have := val_sub_one_lt g e he (u : ℤ_[g]) hu'
    simpa [μ] using this
  refine ⟨(Units.map (PadicInt.toZMod (p := g)).toMonoidHom).liftOfSurjective (units_toZMod_surj g) ⟨μ, hker⟩, ?_⟩
  intro u
  exact ((Units.map (PadicInt.toZMod (p := g)).toMonoidHom).liftOfRightInverse_comp_apply _
    (Function.rightInverse_surjInv (units_toZMod_surj g)) ⟨μ, hker⟩ u).symm

end GlobalTheory.TameRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumPairClassesExplicit
section
noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem datLoc_classes : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie Xi muT hL i hi c c'
  have hi0 : i ≤ D.R.m := Nat.le_of_succ_le hi
  have hlt : i < D.R.m := hi
  have h1 : (1 : GL (Fin (D.R.N i)) D.host.E) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi0) := one_mem _
  have h1' : (1 : GL (Fin (D.R.N (i + 1))) D.host.E) ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi) := one_mem _
  have hx : ((St i hi0).y c).1 = ratA D.host.F (1 : GL (Fin (D.R.N i)) D.host.E) * ((St i hi0).y c).1 * (1 : ((St i hi0).K ((St i hi0).chOf c)).lev.U).1 := by
    simp
  have hx' : ((St (i + 1) hi).y c').1 = ratA D.host.F (1 : GL (Fin (D.R.N (i + 1))) D.host.E) * ((St (i + 1) hi).y c').1 * (1 : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U).1 := by
    simp
  have hu' := _root_.GlobalTheory.TwV.ratIsometry_unitary A dtU a hP hTie (i + 1) hi 1 h1'
  have hu := _root_.GlobalTheory.TwV.ratIsometry_unitary A dtU a hP hTie i hi0 1 h1
  have hl := _root_.GlobalTheory.TwV.latK_lev_rat A dtU a hP hTie i hi0 c ((St i hi0).y c) 1 h1 1 hx
  have hl' := _root_.GlobalTheory.TwV.latK_lev_rat A dtU a hP hTie (i + 1) hi c' ((St (i + 1) hi).y c') 1 h1' 1 hx'
  have hd := _root_.GlobalTheory.TwV.adelicDatum_at_translates A dtU a hP hTie Xi muT hL i hi c c' ((St i hi0).y c) ((St (i + 1) hi).y c') 1 h1 1 h1' 1 1 hx hx' hu'
  have hloc := hL.loc i hi ((St i hi0).chOf c) ((St (i + 1) hi).chOf c') ((St i hi0).y c) ((St (i + 1) hi).y c')
  rw [hl, hl'] at hloc
  refine _root_.GlobalTheory.TwV.datLoc_of_move D t.cc (ssRec t u μ) (t.rd u μ).lev _ _ (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x)) _ _ hu hu' ?_
  have hE : Xi i hi ((St i hi0).chOf c) ((St (i + 1) hi).chOf c') ((St i hi0).y c) ((St (i + 1) hi).y c') = _ := funext fun z => by
    have := hd z
    simpa [(hL.mu_mul i hlt).1, -Matrix.toLin'_toMatrix'] using this
  rw [hE] at hloc
  exact hloc

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem kerEntTied_true_ent : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → EntOk E O → (∀ u w h, ThAtServed (ex.ker u w h) E) → ∃ t : KerEntTied ex, I.StdKerTie l Z t ∧ t.O = O ∧ t.ent = E ∧ t.Adapted ∧ t.TopPinned := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex O E hQ hStd hU hE hS
  obtain ⟨t, ht, hO, -, hTop⟩ := _root_.GlobalTheory.Mem.Col2.TC.kerEntTied_true I hOk hP l Z L hT Gi Gl K Y cX ex O E hQ hStd hU hE hS
  exact kerEntTied_withEnt I l Z O E hE hS t ht hO hTop

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharacterNormOneEqInfinityTypeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelChainCharacter_normOne_eq_infinityType : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨i, hi⟩) ∧ ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj (z : D.host.E) = 1 → ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 = ratId D.host.F D.host.E z → (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ) := by
  first | exact @GlobalTheory.TwV.mt_ratId | exact GlobalTheory.TwV.mt_ratId | (intros; apply GlobalTheory.TwV.mt_ratId <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelChainCharactersAlgebraicUnitaryPointsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelChainCharacters_algebraic_unitaryPoints : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar) := by
  first | exact @GlobalTheory.TieAlgValues.mt_mem_Qbar | exact GlobalTheory.TieAlgValues.mt_mem_Qbar | (intros; apply GlobalTheory.TieAlgValues.mt_mem_Qbar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelCoefficientFieldLeCoefficientField
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem kerField_le_rec :
    ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∀ y : t.X.K, ∃ k : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL k = t.seam.σ₀ y := by
  intro B X I _ _ l Z L hT Gi Gl K Y cX ex t hS y
  obtain ⟨hX, hseam⟩ := And.intro hS.X_eq hS.seam
  clear hS
  cases t
  dsimp only at hX hseam y ⊢
  subst hX
  have h := eq_of_heq hseam
  subst h
  exact ⟨y, rfl⟩

end GlobalTheory.TwU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeEqAwayFromPrimeOfAgreeOffPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLattice_eq_away_from_prime_of_agree_off_place : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (n p : ℕ) [Fact p.Prime] (G : GAtP p) (A : LocAt D.host.F D.host.E n G), LocInt A → SplAlg A → ∀ v (P : HeightOneSpectrum (𝓞 D.host.E)), PrimeOf p (G.P.W v) (A.iw v) P → ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) D.host.E) (a : 𝓞 D.host.E) (Lb : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Module.Finite (𝓞 D.host.E) Lb → Submodule.span D.host.E (Lb : Set (Fin N → D.host.E)) = ⊤ → ∀ x x' : GL (Fin N) (AfE D.host.F D.host.E), SameOff (A.pl v).1 x x' → GL3Theta.EqOff D P (latK D.sp J a x Lb) (latK D.sp J a x' Lb) := by
  first | exact @GlobalTheory.TwV.Xc.eqOff_latK_of_sameOff | exact GlobalTheory.TwV.Xc.eqOff_latK_of_sameOff | (intros; apply GlobalTheory.TwV.Xc.eqOff_latK_of_sameOff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatKRatMulLev
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem latK_rat_mul_lev : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (N : ℕ) (J : Matrix (Fin N) (Fin N) D.host.E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (a : 𝓞 D.host.E) (x : GL (Fin N) (AfE D.host.F D.host.E)) (κ : S.U), ∀ g ∈ UJ (sigD D : D.host.E →+* D.host.E) J, latK D.sp J a (GlobalTheory.TwU.ratA D.host.F g * x * κ.1) S.Lb = SDLat.smulLat (eMat rfl (D.sp.cm.sig : D.host.E →+* D.host.E) J g) (latK D.sp J a x S.Lb) := by
  intro D N J T f bad S a x κ g hg
  letI := D.host.cmStar
  rw [Formalism.MainNotions.G.KAat.latK_tr _ _ _ _ _ g hg (GlobalTheory.TwU.hatStab_of_lev S κ)]
  unfold SDLat.smulLat eMat
  congr 1
  ext v
  simp [Matrix.toLin'_toMatrix']

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixStepDatumEquivariantRationalUnitaryStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixStepDatum_equivariant_rational_unitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), i < t.m2 → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  first | exact @GlobalTheory.RatEntry.xiPt_rat | exact GlobalTheory.RatEntry.xiPt_rat | (intros; apply GlobalTheory.RatEntry.xiPt_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaCMCurveTheoremsOfAlgebraicTranslaStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedThetaCMCurveTheorems_of_algebraicTranslates : Formalism.L2.KerInert.AlgTAll → GlobalTheory.ThLoc.Inputs := by
  first | exact @GlobalTheory.ThLoc.inputs_of_algT | exact GlobalTheory.ThLoc.inputs_of_algT | (intros; apply GlobalTheory.ThLoc.inputs_of_algT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceComponentPullbackLatticeVectorMemDualSpanStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeComponent_pullback_latticeVector_mem_dual_span : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ latAd x.1 lev.Lb →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  first | exact @GlobalTheory.AwayLat.prV_pullV_mem_latS_dual | exact GlobalTheory.AwayLat.prV_pullV_mem_latS_dual | (intros; apply GlobalTheory.AwayLat.prV_pullV_mem_latS_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceUnderTwistPrimeOverTupleRamifiedPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.UnderQp

theorem mem_QE_of_heq {B : Base} {X : PreX B.toPre} (I : TC B X) {Xf : Fields} (hX : Xf = B.fields) {S : Set ℕ} (hS : S = I.S)
    {sel : HeightOneSpectrum (𝓞 Xf.F) → HeightOneSpectrum (𝓞 Xf.E)} (hsel : HEq sel I.sel)
    {tup : I.ι → Tup Xf.F Xf.E Xf.K S} (htup : HEq tup I.tup) (a : I.ι) (P : HeightOneSpectrum (𝓞 B.fields.E))
    (hP : P ∈ I.Q a) (q : ℕ) (hq : (q : 𝓞 B.fields.E) ∈ P.asIdeal) :
    ∃ P' ∈ QE sel (tup a : Chr Xf.F Xf.E Xf.K), (q : 𝓞 Xf.E) ∈ P'.asIdeal := by
  subst hX
  subst hS
  cases hsel
  cases htup
  exact ⟨P, hP, hq⟩

theorem underQ_qp : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∀ (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), I.UnderQ a v → ∃ q ∈ Y.Qp a, ((q : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
  intro B X I _ _ l Z L hT Gi Gl K Y cX ex t hSK a v hv
  obtain ⟨P, hP, hPv⟩ := hv
  have hN1 : Ideal.absNorm P.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact P.isPrime.ne_top
  set q := (Ideal.absNorm P.asIdeal).minFac with hqdef
  have hqp : q.Prime := Nat.minFac_prime hN1
  have hqP : (q : 𝓞 B.fields.E) ∈ P.asIdeal :=
    GlobalTheory.KerTie.natCast_mem_of_prime_dvd_absNorm P hqp (Nat.minFac_dvd _)
  refine ⟨q, ?_, ?_⟩
  · exact (t.Q_rec a q).2 ⟨hqp, mem_QE_of_heq I hSK.X_eq hSK.S hSK.sel hSK.tup a P hP q hqP⟩
  · rw [← hPv]
    show (q : 𝓞 B.host.F) ∈ P.asIdeal.comap (algebraMap (𝓞 B.host.F) (𝓞 B.host.E))
    rw [Ideal.mem_comap, map_natCast]
    exact hqP

end GlobalTheory.TwU.UnderQp
end

