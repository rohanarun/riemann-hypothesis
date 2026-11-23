module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfOfDecoRaw
public import Formalism.LocalToGlobal.Columns.RecLevelDiv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0327
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoxFinitePosProductHaarUnitaryGroups
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem haar_box_prod_finite_pos : ∀ (ι : Type) [Fintype ι] (p q : ι → ℕ) (m : ∀ i, Measure (UpqT (p i) (q i))), (∀ i, (m i).IsHaarMeasure) → ∃ B : ∀ i, Set (UpqT (p i) (q i)), (∀ i, MeasurableSet (B i)) ∧ ∏ i, m i (B i) ≠ 0 ∧ ∏ i, m i (B i) ≠ ⊤ := by
  intro ι _ p q m hm
  have hK : ∀ i, ∃ K : Set (UpqT (p i) (q i)), IsCompact K ∧ K ∈ nhds (1 : UpqT (p i) (q i)) :=
    fun i => exists_compact_mem_nhds 1
  choose K hKc hKn using hK
  refine ⟨fun i => interior (K i), fun i => isOpen_interior.measurableSet, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    exact (isOpen_interior.measure_pos (m i) ⟨1, mem_interior_iff_mem_nhds.mpr (hKn i)⟩).ne'
  · apply ENNReal.prod_ne_top
    intro i _
    exact (lt_of_le_of_lt (measure_mono interior_subset) (hKc i).measure_lt_top).ne

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCopy
section
noncomputable section

namespace GlobalTheory.SeeSaw.TopLevel

section Gen

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix
open scoped TensorProduct

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]

theorem lev_iff (hc : CMData F E) {n n' : ℕ} (e : n' = n) [NeZero n] {J' : Matrix (Fin n') (Fin n') E} {J : Matrix (Fin n) (Fin n) E}
    (hJ' : J' = 1) (hJ : J = 1) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad)
    (hL : S.Lb = Formalism.L2.Col.stdLat E n) {r t s : ℕ} (h : r ≤ n) (h' : r ≤ n') (ht : 0 < t) (hn : n = r + s * t) {SG : Finset (Pl E)}
    (P : LevFam E K r SG) (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ) (emb : K →+* ℂ)
    (hR : RdLev hc S.U S.chi Set.univ (parFam h t s P χ) emb) (P' : LevelP SG r ℂ)
    (cg : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ) (xq : ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ)
    (hH : ∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (P w).H)
    (hchi : ∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (P w).H), ((P'.chi g : ℂˣ) : ℂ) = ∏ w, emb (((P w).lam ⟨g.1 w, hg w⟩ : Kˣ) : K))
    (hcg : ∀ c (w : SG) a, ((cg (c + 1) w.1 a : ℂˣ) : ℂ) = emb ((χ w c a : Kˣ) : K))
    (g : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hgy : ∀ i j, g.1 i j = y.1 (finCongr e i) (finCongr e j)) :
    (g ∈ lev hc J' 1 ⟨r, h', t, s, SG, ∅, P', cg, xq⟩ ↔ y ∈ S.U) ∧
      ∀ hy : y ∈ S.U, ((levFn 1 ⟨r, h', t, s, SG, ∅, P', cg, xq⟩ g : ℂˣ) : ℂ) = star ((S.chi ⟨y, hy⟩ : ℂˣ) : ℂ) := by
  classical
  subst e hJ' hJ
  obtain rfl : g = y := Units.ext (Matrix.ext hgy)
  have e0 : g ∈ lev hc 1 1 ⟨r, h', t, s, SG, ∅, P', cg, xq⟩ ↔ g ∈ lev hc 1 1 (parDat h t s P χ) := by
    rw [mem_lev, mem_lev, mem_parLev, mem_parLev]
    refine and_congr Iff.rfl ((hH _).trans ⟨fun h w _ => h w, fun h w => h w (Set.mem_univ w)⟩)
  have hred : ∀ (hz : g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F))) (w : Pl E), redFn 1 w g = redAt 1 w ⟨g, hz⟩ :=
    fun hz w => extendOne_of_mem _ hz
  have hU : g ∈ S.U → g ∈ UAd hc n' ∧ g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) := fun hy => by
    obtain ⟨h1, h2⟩ := (S.U_eq g).1 hy
    refine ⟨h1, rll_St_of_loc n' g fun v => ⟨_, rll_put_mem_St n' v ?_, rll_put_self n' v _⟩⟩
    have := (S.Uloc_lev v (h2 v)).2
    rw [hL] at this
    exact this
  have e1 : g ∈ levU hc n' ∅ SG (parFam h t s P χ).grp ↔ g ∈ S.U := by
    rw [mem_levU_iff]
    constructor
    · rintro ⟨h1, h2, -, h4⟩
      exact (hR g h2 h1 fun v hv => absurd (Set.mem_univ v) hv).1.2 fun w => hred h2 w.1 ▸ h4 w (Set.mem_univ w)
    · intro hy
      obtain ⟨h1, h2⟩ := hU hy
      refine ⟨h1, h2, fun P hP => absurd hP (Finset.notMem_empty P), fun w _ => ?_⟩
      have := (hR g h2 h1 fun v hv => absurd (Set.mem_univ v) hv).1.1 hy w
      rwa [← hred h2] at this
  refine ⟨by rw [e0, ← levU_parFam_eq_lev hc h ht hn, e1], fun hy => ?_⟩
  obtain ⟨h1, h2⟩ := hU hy
  have h3 := e1.2 hy
  have h4 : g ∈ lev hc 1 1 (parDat h t s P χ) := levU_parFam_eq_lev hc h ht hn P χ ▸ h3
  have h5 := e0.2 h4
  obtain ⟨r1, r2⟩ := hR g h2 h1 fun v hv => absurd (Set.mem_univ v) hv
  have a1 : ((levFn 1 ⟨r, h', t, s, SG, ∅, P', cg, xq⟩ g : ℂˣ) : ℂ) = emb ((levFn 1 (parDat h t s P χ) g : Kˣ) : K) := by
    unfold levFn
    rw [extendOne_of_mem _ h5.2, extendOne_of_mem _ h4.2]
    simp only [Units.val_mul, Units.coe_prod, map_mul, map_prod]
    congr 1
    congr 1
    · rw [hchi _ fun w => h4.2 w (Set.mem_univ w)]
      have := rld_ofLocal_chi (fun w => (P w).H) (fun w => (P w).lam) ⟨_, h4.2⟩
      refine Eq.trans ?_ (congrArg (fun x : Kˣ => emb (x : K)) this).symm
      simp only [Units.coe_prod, map_prod]
      rfl
    · show ∏ PP ∈ SG, _ = ∏ PP ∈ SG, _
      refine Finset.prod_congr rfl fun w hw => ?_
      show ∏ c ∈ Finset.range s, _ = ∏ c ∈ Finset.range s, _
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [rld_parDat_cg h P χ c ⟨w, hw⟩]
      exact hcg c ⟨w, hw⟩ _
  have a2 := levChr_parFam_eq_levChar hc h ht hn P χ g h3 h4
  rw [levChar_apply] at a2
  rw [a1, ← a2, r2 hy (r1.1 hy)]
  show emb ((piChar (fun w => (parFam h t s P χ w).H) (fun w => (parFam h t s P χ w).lam) (levRed hc n' ∅ SG _ ⟨g, h3⟩) : Kˣ) : K) = _
  rw [piChar_apply, Units.coe_prod, map_prod, star_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : Finite (𝓞 E ⧸ w.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  have b1 := ((emb.toMonoidHom.comp ((Units.coeHom K).comp (parFam h t s P χ w).lam)).isOfFinOrder
    (isOfFinOrder_of_finite ⟨_, r1.1 hy w⟩)).norm_eq_one
  refine Eq.trans ?_ ((congrArg star (Complex.inv_eq_conj b1)).trans (Complex.conj_conj _)).symm
  exact congrArg (fun x => emb (((parFam h t s P χ w).lam x : Kˣ) : K))
    (Subtype.ext ((levRed_apply hc n' ∅ SG _ ⟨g, h3⟩ w).trans (hred h2 w.1)))

theorem exists_copy {A : Type} [CommRing A] {n n' : ℕ} (e : n' = n) (g : GL (Fin n') A) :
    ∃ y : GL (Fin n) A, ∀ i j, g.1 i j = y.1 (finCongr e i) (finCongr e j) := by
  subst e
  exact ⟨g, fun _ _ => rfl⟩


attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar in
set_option maxHeartbeats 1000000 in
theorem rd_all {B : Base} {X : PreX B.toPre} (I : TC B X) [NeZero (B.R.N B.R.m - 1)] {Lb U chi y lat st}
    (h : I.ReadsP I.mu0 Lb U chi y lat st) (c : (I.stX I.mu0).Cl) :
    RdLev (E := B.fields.E) B.sp.cm U chi Set.univ (rowTyG I.Ch I.Ps) B.embLL :=
  haveI : IsEmpty (I.Q I.mu0) := by rw [I.twistPrimes_reference_tuple_eq_empty]; infer_instance
  rdLev_of_reads (X := B.fields) (hc := B.sp.cm) (bad := Set.univ) (rowTyG I.Ch I.Ps) (levQX B.R I.sel (I.tup I.mu0))
    B.embLL (U := U) (chi := chi) (y := y c) (k := 1) (p := ((I.stX I.mu0).rep c).1.1) (by rw [mul_one]; exact h.pt c)
    (fun v _ => map_one _) (fun P hP => absurd hP (Finset.notMem_empty _))
    (fun x q hq => h.lev c x q (by rwa [mul_one] at hq))
    (fun x κ h1 h2 => h.chr c x κ h1 (by rwa [mul_one] at h2))

end Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


end GlobalTheory.SeeSaw.TopLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFractionalIdealOfHermIdele
section
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct nonZeroDivisors

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SeeSaw.IdeleIdeal

variable {D : D7}

theorem one_tmul_mem (o : 𝓞 D.host.E) : (1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E) ∈ intAE D :=
  GlobalTheory.FinPl.Conductor.tmul_mem (fun v => by rw [map_one]; exact one_mem _) o

theorem one_tmul_mem_iff (e : D.host.E) :
    (1 : Af D.host.F) ⊗ₜ[D.host.F] e ∈ intAE D ↔ e ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  have h : finPart D (incA D e) = (1 : Af D.host.F) ⊗ₜ[D.host.F] e := by
    change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  rw [← h]
  exact (GlobalTheory.SplitDec.int_iff (incA D e)).trans (GlobalTheory.SplitDec.rat_int_iff e)

theorem exists_int_mul (y : Af D.host.F ⊗[D.host.F] D.host.E) : ∃ N : 𝓞 D.host.E, N ≠ 0 ∧
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * y ∈ intAE D := by
  obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.FinPl.Conductor.approx y
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  have hb0 : (b : D.host.E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  rw [mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  refine add_mem ?_ (GlobalTheory.FinPl.Conductor.mul_mem_int (one_tmul_mem b) hu)
  have e : (b : D.host.E) * x = (a : D.host.E) := by
    rw [← hab]; field_simp
  rw [e]
  exact one_tmul_mem a

theorem approx_mul (z : Af D.host.F ⊗[D.host.F] D.host.E) {N : 𝓞 D.host.E} (hN : N ≠ 0) :
    ∃ x : D.host.E, ∃ u ∈ intAE D,
    z = (1 : Af D.host.F) ⊗ₜ[D.host.F] x + ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * u := by
  have hN' : (N : D.host.E) ≠ 0 := by exact_mod_cast hN
  obtain ⟨x, u, hu, e⟩ := GlobalTheory.FinPl.Conductor.approx
    (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)⁻¹) * z)
  refine ⟨N * x, u, hu, ?_⟩
  have h1 : ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)⁻¹) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hN']; rfl
  calc z = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) *
        (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)⁻¹) * z) := by rw [← mul_assoc, h1, one_mul]
    _ = _ := by rw [e, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end GlobalTheory.SeeSaw.IdeleIdeal

namespace GlobalTheory.SeeSaw.IdeleIdeal

variable {D : D7}

def subOf (y : Af D.host.F ⊗[D.host.F] D.host.E) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {d | y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D}
  add_mem' {a b} ha hb := by
    show y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (a + b)) ∈ intAE D
    rw [TensorProduct.tmul_add, mul_add]; exact add_mem ha hb
  zero_mem' := by
    show y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (0 : D.host.E)) ∈ intAE D
    rw [TensorProduct.tmul_zero, mul_zero]; exact zero_mem _
  smul_mem' c d hd := by
    show y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c • d)) ∈ intAE D
    have e : y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c • d)) =
        ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) * (y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d)) := by
      rw [Algebra.smul_def, ← mul_assoc, mul_comm _ y, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e]
    exact GlobalTheory.FinPl.Conductor.mul_mem_int (one_tmul_mem c) hd

theorem mem_subOf {y : Af D.host.F ⊗[D.host.F] D.host.E} {d : D.host.E} :
    d ∈ subOf y ↔ y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D := Iff.rfl

theorem isFractional_subOf {y y' : Af D.host.F ⊗[D.host.F] D.host.E} (h : y' * y = 1) :
    IsFractional (𝓞 D.host.E)⁰ (subOf y) := by
  obtain ⟨N, hN, hNy⟩ := exists_int_mul y'
  refine ⟨N, mem_nonZeroDivisors_of_ne_zero hN, fun d hd => ?_⟩
  have e : (1 : Af D.host.F) ⊗ₜ[D.host.F] (N • d) =
      (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * y') * (y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d)) := by
    rw [mul_assoc, ← mul_assoc y', h, one_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def]
  have := GlobalTheory.FinPl.Conductor.mul_mem_int hNy (mem_subOf.1 hd)
  rw [← e, one_tmul_mem_iff, Submodule.mem_one] at this
  obtain ⟨r, hr⟩ := this
  exact ⟨r, hr⟩

def idealOf {y y' : Af D.host.F ⊗[D.host.F] D.host.E} (h : y' * y = 1) : FI D := ⟨subOf y, isFractional_subOf h⟩

theorem mem_idealOf {y y' : Af D.host.F ⊗[D.host.F] D.host.E} (h : y' * y = 1) {d : D.host.E} :
    d ∈ idealOf h ↔ y * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D := Iff.rfl

end GlobalTheory.SeeSaw.IdeleIdeal


open GlobalTheory.SeeSaw.IdeleIdeal GlobalTheory.FinPlLoc in
theorem GlobalTheory.SeeSaw.exists_idealOfIdele : ∀ (D : D7) (m : (AE D)ˣ), ∃ 𝔞 : FI D, ∀ x : Pl D, ∀ a ∈ idAt D (· = x),
    a ∈ idV 𝔞 x ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  intro D m
  set mi := finPart D ((m⁻¹ : (AE D)ˣ) : AE D) with hmi
  set mf := finPart D (m : AE D) with hmf
  have hmm : mf * mi = 1 := by
    rw [hmf, hmi, ← map_mul, Units.mul_inv, map_one]
  refine ⟨idealOf hmm, fun x a ha => ?_⟩
  have hmemA : ∀ d : D.host.E, d ∈ (idealOf hmm) ↔
      mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) ∈ intAE D := fun d => mem_idealOf hmm
  constructor
  · intro hv
    refine ⟨Ideal.mul_mem_left _ _ ha, ?_⟩
    rw [map_mul, ← hmi]
    clear ha
    induction hv using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, -, d, hd, rfl⟩ := hy
      rw [finPart_pair]
      have e : mi * (α ⊗ₜ[D.host.F] d) = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * (mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d)) := by
        rw [mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [e]
      have h1 : α ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D := by
        simpa using GlobalTheory.FinPl.Conductor.tmul_mem hα (1 : 𝓞 D.host.E)
      exact GlobalTheory.FinPl.Conductor.mul_mem_int h1 ((hmemA d).1 hd)
    | zero => rw [map_zero, mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _), mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg, mul_neg]; exact neg_mem hy
  · intro hi
    have hz : mi * finPart D a ∈ intAE D := by
      have := hi.2
      rwa [map_mul, ← hmi] at this
    obtain ⟨N, hN, hNm⟩ := exists_int_mul mi
    obtain ⟨d, u, hu, e⟩ := approx_mul (finPart D a) hN
    have hd : d ∈ (idealOf hmm) := by
      rw [hmemA]
      have e2 : mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] d) =
          mi * finPart D a - (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * mi) * u := by
        rw [e]; ring
      rw [e2]
      exact sub_mem hz (GlobalTheory.FinPl.Conductor.mul_mem_int hNm hu)
    have hidem : (singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a = finPart D a :=
      GlobalTheory.FinPl.Conductor.idem_mul x _ fun w hw => (Submodule.mem_iInf _).1 (Ideal.mem_inf.1 ha).2 ⟨w, hw⟩
    have hε : singleV D.host.F x 1 ∈ intAf D.host.F := by
      have := GlobalTheory.FinPl.Conductor.idem_mul_mem (v := x) (α := 1) (by rw [map_one]; exact one_mem _)
      rwa [mul_one] at this
    have hsupp : ∀ (β : Af D.host.F) w, w ≠ x → evalV D.host.F w (singleV D.host.F x 1 * β) = 0 := fun β w hw => by
      rw [map_mul, GlobalTheory.FinPl.Conductor.ev_ne hw, zero_mul]

    have hrest : ∀ u ∈ intAE D, finIn D ((singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) *
        (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * u)) ∈ idV (idealOf hmm) x := by
      intro u hu
      induction hu using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨β, hβ, o, rfl⟩ := hy
        have e3 : (singleV D.host.F x 1 ⊗ₜ[D.host.F] (1 : D.host.E)) *
            (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * (β ⊗ₜ[D.host.F] (o : D.host.E))) =
            (singleV D.host.F x 1 * β) ⊗ₜ[D.host.F] ((N : D.host.E) * o) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
        rw [e3, finIn_tmul]
        refine AddSubgroup.subset_closure ⟨_, GlobalTheory.FinPl.Conductor.idem_mul_mem (hβ x), hsupp β, _, ?_, rfl⟩
        rw [hmemA]
        have e4 : mi * ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : D.host.E) * o)) =
            (((1 : Af D.host.F) ⊗ₜ[D.host.F] (N : D.host.E)) * mi) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E)) := by
          rw [mul_comm _ mi, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [e4]
        exact GlobalTheory.FinPl.Conductor.mul_mem_int hNm (one_tmul_mem o)
      | zero => rw [mul_zero, mul_zero, map_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [mul_add, mul_add, map_add (f := _)]; exact add_mem hy hz
      | neg y _ hy => rw [mul_neg, mul_neg, map_neg]; exact neg_mem hy
    rw [eq_finIn (infPart_of_idAt ha), ← hidem, e, mul_add, map_add (f := _)]
    refine add_mem ?_ (hrest u hu)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, finIn_tmul]
    exact AddSubgroup.subset_closure ⟨_, hε, fun w hw => GlobalTheory.FinPl.Conductor.ev_ne hw, d, hd, rfl⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.PinInhab

section SlopeTestRemainingChoices
open GlobalTheory.FinPl (SplitPt idAt idOff grpAt grpOff congGrp compAt)
open GlobalTheory.IdemSupport GlobalTheory.LocMod.SevPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_add (q : SplitPt D k) : q.e * (q.e + cA D q.e) = q.e := by
  obtain ⟨h1, h2, -⟩ := q.split
  rw [mul_add, h1, h2, add_zero]

theorem v_eq_under (q : SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt q.e P) :
    q.v = P.under (𝓞 D.host.F) := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨ε, hε, hs⟩ := q.above
  by_contra hne
  have h0 := (place_comp hΦ hε).2.2 P (fun e => hne e.symm)
  have h1 := ev_mul (Φ := Φ) q.e (q.e + cA D q.e) P
  rw [e_mul_add, hs, h0, mul_zero, (delta_of_isIdemAt hΦ h).2.1] at h1
  exact one_ne_zero h1

theorem idem_unique {P : HeightOneSpectrum (𝓞 D.host.E)} {e e' : Formalism.L2.Theta.AE D} (h : Formalism.L2.NTheta.IsIdemAt e P)
    (h' : Formalism.L2.NTheta.IsIdemAt e' P) : e = e' := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := delta_of_isIdemAt hΦ h
  have hd' := delta_of_isIdemAt hΦ h'
  refine hΦ.ext' (by rw [hd.1, hd'.1]) fun Q => ?_
  by_cases hQ : Q = P
  · subst hQ; rw [hd.2.1, hd'.2.1]
  · rw [hd.2.2 Q hQ, hd'.2.2 Q hQ]

theorem mem_congGrp {V : HSp D} {I : Ideal (Formalism.L2.Theta.AE D)} {g : GA D V} :
    g ∈ congGrp V I ↔ ∀ i j, (mt V g - 1) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (Formalism.L2.Theta.AE D ⧸ I) => x.1 i j) h
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem mem_idAt_of_supp (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {a : Formalism.L2.Theta.AE D}
    (h : (q.e + cA D q.e) * a = a) : a ∈ idAt D P := by
  obtain ⟨ε, hε, hs⟩ := q.above
  have h1 := ((GlobalTheory.FinPl.placeIdem_acts D q.v ε hε).1 a).2 (hs ▸ h)
  rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at h1 ⊢
  exact ⟨h1.1, fun w hw => h1.2 w fun e => hw (e ▸ hP)⟩

theorem pr_eq_zero_of_off (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {a : Formalism.L2.Theta.AE D}
    (ha : a ∈ idOff D P) : q.pr a = 0 := by
  have he : q.e ∈ idAt D (· = q.v) := mem_idAt_of_supp q (P := (· = q.v)) rfl (by rw [mul_comm, e_mul_add])
  rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at he
  have hv : compAt D q.v a = 0 := by
    unfold idOff at ha
    rw [Submodule.mem_iInf] at ha
    exact RingHom.mem_ker.1 (ha ⟨q.v, hP⟩)
  refine pr_eq_zero q (GlobalTheory.FinPl.CMAdele_eq_zero_of_infinite_and_finite_components_zero D _ ?_ fun w => ?_)
  · rw [RingHom.map_mul, he.1, zero_mul]
  · rw [RingHom.map_mul]
    by_cases hw : w = q.v
    · rw [hw, hv, mul_zero]
    · rw [he.2 w hw, zero_mul]

theorem map_mt_eq_one_of_off (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {V : HSp D} {g : GA D V}
    (hg : g ∈ grpOff V P) : (mt V g).map q.pr = 1 := by
  ext i j
  have h1 := pr_eq_zero_of_off q hP (mem_congGrp.1 hg i j)
  rw [Matrix.sub_apply, map_sub] at h1
  rw [Matrix.map_apply, sub_eq_zero.1 h1]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

end SlopeTestRemainingChoices

end GlobalTheory.LocMod.PinInhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatDoubledPairSchrodingerFunctionStatement
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhat_doubledPairSchrodingerFunction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat (sch ψ A B ν 𝓨 f) := by
  first | exact @GlobalTheory.SchwartzSch.isSchwartzBruhat_sch | exact GlobalTheory.SchwartzSch.isSchwartzBruhat_sch | (intros; apply GlobalTheory.SchwartzSch.isSchwartzBruhat_sch <;> assumption)
end

