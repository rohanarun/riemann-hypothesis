module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValueLatticeAddSubgroupSmulMoveLaws
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvSmulMemOfRedL
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
public import Formalism.LocalToGlobal.Columns.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntPOfKerP
section
noncomputable section

namespace GlobalTheory.LvT.Built.IntPPass

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem ev_smul {D : D7} {u : D.what₂.Word} (B : Built.Dat D u) (i : ℕ) (c : D.what₂.LL) (F : B.V i) :
    B.ev i (c • F) = D.what₂.embLL c • B.ev i F := by
  unfold Built.Dat.ev
  exact map_smulₛₗ _ _ _

theorem intP_of_kerP : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerP k → K.IntP Co Co' := by
  intro D u B i sp sp' M M' R R' k Co Co' K hT hK hCo hCo' hV hV' hP w hw hs p p' y hy
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  set g := R.zeta ζ with hg
  set g' := R'.zeta ζ' with hg'
  have h0 := (GlobalTheory.LvT.ValEq.valB_laws D u B.ch i M Co hCo w hw ∅ (g • R.pt b d)).2.2.2 g⁻¹ y hy
  rw [inv_smul_smul] at h0
  set y₀ := M.act g⁻¹ y with hy₀
  have hyy : y = M.act g y₀ := by
    rw [hy₀, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨F, hF, hFy⟩ := (hV.dual w hw b d y₀).1 h0
  have h1 := hP w hw hs b b' d d' F hF
  have h2 := hK b b' d d' F y₀ hFy
  rw [hT, hyy, K.src, ← map_smul]
  refine (GlobalTheory.LvT.ValEq.valB_laws D u B.ch (i + 1) M' Co' hCo' w hw Finset.univ (R'.pt b' d')).2.2.2 g' _ ?_
  refine (hV'.ker w hw hs b' d' _).2 ⟨_, h1, ?_⟩
  rw [ev_smul, ← h2, map_zpow₀, map_natCast]
  rfl

end GlobalTheory.LvT.Built.IntPPass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OffOfNotMem
section
noncomputable section

namespace GlobalTheory.LvT.Built.SplitPts

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem exists_ufGL {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : GL (Fin n) E)
    (h : (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1) : ∃ g : UF E n, ufGL E n g = γ := by
  obtain ⟨e, rfl⟩ := (toGLm E n).surjective γ
  refine ⟨⟨e, fun x y => ?_⟩, rfl⟩
  rw [← toGLm_mulVec e x, ← toGLm_mulVec e y]
  show star ((toGLm E n e : Matrix (Fin n) (Fin n) E) *ᵥ x) ⬝ᵥ ((toGLm E n e : Matrix (Fin n) (Fin n) E) *ᵥ y) = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

theorem sameOff_gmap {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 E))}
    {N N' : Submodule (𝓞 E) (Sp E n)} (g : Sp E n ≃ₗ[E] Sp E n) (h : SameOff ST N N') :
    SameOff ST (gmap g N) (gmap g N') := fun w hw => by
  ext x
  rw [mem_localization_gmap, mem_localization_gmap, h w hw]

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}

theorem notMem_QE (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) : (p : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro hm
  unfold QE at hP
  split_ifs at hP with hf
  swap
  · simp at hP
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
  have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := (Set.Finite.mem_toFinset hf).1 hv
  have hg : GoodPl X.E S v := by
    by_contra hn
    have := (Subgroup.mem_inf.1 mu.2).2
    exact hv' (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 this v) hn)
  apply hg.2.2
  have h1 : (p : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hs v, Ideal.mem_under]
    simpa using hm
  have h2 : ((p : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h1
  have h3 := (ringChar.spec _ p).1 h2
  have h4 : ringChar (𝓞 X.F ⧸ v.asIdeal) = p :=
    ((Nat.dvd_prime hp).1 h3).resolve_left CharP.ringChar_ne_one
  show ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
  rwa [h4]

variable (sel) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (i : ℕ)

def offSetoid : Setoid (PtAt R sel mu cst u i) where
  r := SameOffPt sel mu cst u
  iseqv :=
    ⟨fun _ => ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      fun h => ⟨fun w hw => (h.1 w hw).symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩,
      fun h h' => ⟨fun w hw => (h.1 w hw).trans (h'.1 w hw), h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
        h.2.2.2.trans h'.2.2.2⟩⟩

theorem off_of_notMem (hPr : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} (h : (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) :
    ∀ P ∈ Pr.vT u, w ≠ P ∧ w ≠ conjPrime₂ P := fun P hP => ne_of_T_notMem hPr u ⟨P, hP⟩ h

theorem ys_congr (hPr : Pr.Ok) (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal)
    {N N' : Submodule (𝓞 X.E) (Sp X.E (R.N i))} (h : SameOff (Pr.vT u) N N') :
    (ysAt R sel mu cst i).ys N' = (ysAt R sel mu cst i).ys N := by
  classical
  have h1 : ∀ w : rowSG Pr sel mu, localization₂ w.1.asIdeal N' = localization₂ w.1.asIdeal N := fun w =>
    (h w.1 (off_of_notMem u hPr
      ((Finset.mem_union.1 w.2).elim (fun h => T_notMem_vGs hPr u ⟨w.1, h⟩) (hQ w.1)))).symm
  unfold ysAt
  split_ifs
  · show ybSet sel mu cst N' = ybSet sel mu cst N
    simp only [ybSet, locLat, h1]
  · rfl

theorem exists_split : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K)), ∃ sp : Split (tdatAt sel mu cst L Tp u i) (Pr.T u), ∀ b p q, (sp.off b).r p q ↔ SameOffPt sel mu cst u p q := by
  intro X Pr R _ Ch sel S mu cst L G m2 u i hX hPr hs hT _ Tp
  classical
  have hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal :=
    fun w hw => notMem_QE hs mu hw (hPr.T_prime u) hT
  have hM := moveHyp_of_ok hPr u
  have hQ' : ∀ (P : Pr.vT u) (w : QE sel (mu : Chr X.F X.E X.K)), w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1 :=
    fun P w => ne_of_T_notMem hPr u P (hQ w.1 w.2)
  have hy := ysAt_off (R := R) sel mu cst hPr u hQ i
  refine ⟨{ off := fun _ => offSetoid sel mu cst u i
            off_act := ?_
            off_lat := fun _ _ _ h => h.1
            ext := ?_
            surj := ?_
            off_up := ?_
            off_dn := ?_
            off_dia := ?_
            dia_deco := ?_
            gam_surj := ?_
            T_mem := fun P hP => (T_unif hX hPr u ⟨P, hP⟩).1
            T_nsq := fun P hP => (T_unif hX hPr u ⟨P, hP⟩).2
            nonconj := fun P hP Q hQ => (hM ⟨P, hP⟩).st ⟨Q, hQ⟩ }, fun _ _ _ => Iff.rfl⟩
  · rintro b g p q ⟨h1, h2, h3, h4⟩
    refine ⟨sameOff_gmap g.1.1 h1, ?_, ?_, ?_⟩
    · funext w x
      show (g.2.1.1 w).1.mulVec (p.1.1.deco.1.be w (g.1.1.symm x)) = (g.2.1.1 w).1.mulVec (q.1.1.deco.1.be w (g.1.1.symm x))
      rw [h2]
    · funext w
      show g.1.1 * p.1.1.fr w * ((g.2.2.1 w)⁻¹).1 = g.1.1 * q.1.1.fr w * ((g.2.2.1 w)⁻¹).1
      rw [h3]
    · show (fun v => g.1.1 v) '' p.1.2 = (fun v => g.1.1 v) '' q.1.2
      rw [h4]
  · rintro b p q ⟨-, h2, h3, h4⟩ h
    have hN := congrArg Deco.N h
    have hf := congrArg Deco.f h
    exact PtY.ext' (Subtype.ext (Deco.ext hN hf h2)) h3 h4
  · intro b p e he h
    have hok := GlobalTheory.LvT.Pts.ok_of_agree p.1.1.deco.2 he
      fun w => h w.1 (off_of_notMem u hPr (T_notMem_vGs hPr u w))
    have hm := PtY.mv_spec p ⟨_, hok⟩ (fun w => (h w.1 (off_of_notMem u hPr (hQ w.1 w.2))).symm)
      (ys_congr sel mu cst u i hPr hQ h)
    have e1 := congrArg Subtype.val hm.1
    refine ⟨PtY.mv p ⟨_, hok⟩, ⟨?_, (congrArg Deco.be e1).symm, hm.2.1.symm, hm.2.2.symm⟩, ?_⟩
    · rw [e1]; exact h
    · have hN := congrArg Deco.N e1
      have hf := congrArg Deco.f e1
      exact Deco.ext hN hf (funext fun w => absurd w.2 (Finset.notMem_empty _))
  · intro b p P x hx hf
    have hm := mv_up (Pr.T u) p P (hM P) (T_unif hX hPr u P) (hQ' P) (hy P) hx hf
    refine ⟨fun w hw => ?_, (congrArg Deco.be hm.1).symm, hm.2.1.symm, hm.2.2.symm⟩
    refine Eq.trans ?_ (congrArg (fun d : Deco X.E _ _ _ => localization₂ w.asIdeal d.N) hm.1).symm
    exact ((upN_spec p.1.1.deco.2.lat p.1.1.deco.2.uni P.1 (hM P).ne hx).2.2.1 w (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm
  · intro b p P g hg
    have e : (tdatAt sel mu cst L Tp u i).deco b p = p.1.1.deco.1.res (Finset.empty_subset _) :=
      Deco.ext rfl rfl (funext fun w => absurd w.2 (Finset.notMem_empty _))
    rw [e] at hg
    have hg' := dn_ok_of_res p.1.1.deco.2 P (hM P) (g := g) hg
    have hm := mv_dn p P (hM P) (hQ' P) (hy P) hg'
    refine ⟨fun w hw => ?_, (congrArg Deco.be hm.1).symm, hm.2.1.symm, hm.2.2.symm⟩
    refine Eq.trans ?_ (congrArg (fun d : Deco X.E _ _ _ => localization₂ w.asIdeal d.N) hm.1).symm
    exact ((p.1.1.deco.2.dnN_spec P (hM P).ne).2.2.1 w (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm
  · intro b p P a
    show SameOffPt sel mu cst u p (PtY.mv p (DecoSet.dia1 P a p.1.1.deco))
    rw [PtY.mv_dia]
    exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  · intro b p P P' a hne
    show (PtY.mv p (DecoSet.dia1 P a p.1.1.deco)).1.1.deco.1.f P' = p.1.1.deco.1.f P'
    rw [PtY.mv_dia]
    funext x
    show ((Pi.mulSingle P a : DiaG (E := X.E) (ST := Pr.vT u)) P').1 * _ = _
    rw [Pi.mulSingle_eq_of_ne hne, Units.val_one, one_mul]
  · intro b γ h
    obtain ⟨g, hg⟩ := exists_ufGL γ h
    exact ⟨(g, 1, 1), hg⟩

end GlobalTheory.LvT.Built.SplitPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrdSubEqOrdDet
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.DetIdlValue

variable {X : Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}

theorem finprod_group {M : Type} [CommMonoid M] (hX : X.Ok) (hsel : IsSel X sel) (g : HeightOneSpectrum (𝓞 X.E) → M)
    (hfin : (Function.mulSupport g).Finite) (h1 : ∀ w, conjPrime₂ w = w → g w = 1) :
    ∏ᶠ w, g w = ∏ᶠ v, g (sel v) * g (conjPrime₂ (sel v)) := by
  classical
  have hu : ∀ v, (sel v).under (𝓞 X.F) = v := fun v => HeightOneSpectrum.ext (hsel v)
  have hu' : ∀ v, (conjPrime₂ (sel v)).under (𝓞 X.F) = v := fun v =>
    HeightOneSpectrum.ext ((GlobalTheory.MuOffMove.under_conjP hX _).trans (hsel v))
  have hsub : Function.mulSupport (fun v => g (sel v) * g (conjPrime₂ (sel v))) ⊆
      (hfin.toFinset.image fun P => P.under (𝓞 X.F) : Finset _) := by
    intro v hv
    rw [Finset.mem_coe, Finset.mem_image]
    by_cases h : g (sel v) = 1
    · refine ⟨conjPrime₂ (sel v), hfin.mem_toFinset.2 fun h' => hv ?_, hu' v⟩
      simp only [h, h', mul_one]
    · exact ⟨sel v, hfin.mem_toFinset.2 h, hu v⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, finprod_eq_prod _ hfin,
    ← Finset.prod_fiberwise_of_maps_to (g := fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F))
      fun P hP => Finset.mem_image_of_mem (fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F)) hP]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hc : conjPrime₂ (sel v) = sel v
  · rw [hc, h1 _ hc, mul_one]
    refine Finset.prod_eq_one fun w hw => h1 w ?_
    by_contra hw'
    have hwv : w.asIdeal.under (𝓞 X.F) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal (Finset.mem_filter.1 hw).2
    rcases ((GlobalTheory.ThetaMove.split_of_conj_ne₂ X w v hX hw' hwv).2 (sel v)).1 (hsel v) with e | e
    · exact hw' (e ▸ hc)
    · rw [e, GlobalTheory.CharValCompare.conjP_conjP] at hc
      exact hw' hc.symm
  · have hsp := (GlobalTheory.ThetaMove.split_of_conj_ne₂ X (sel v) v hX hc (hsel v)).2
    rw [← Finset.prod_pair (Ne.symm hc)]
    refine Finset.prod_subset (fun w hw => ?_) fun w hw hw' => ?_
    · rw [Finset.mem_insert, Finset.mem_singleton]
      exact (hsp w).1 (congrArg HeightOneSpectrum.asIdeal (Finset.mem_filter.1 hw).2)
    · by_contra hg
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      exact hw' (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hg, HeightOneSpectrum.ext ((hsp w).2 hw)⟩)

theorem pow_toNat_mul {G : Type} [CommGroup G] (a : G) (k : ℤ) : a ^ k.toNat * a⁻¹ ^ (-k).toNat = a ^ k := by
  rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_sub, Int.toNat_sub_toNat_neg]

private theorem span_eq_top_of_isSdLat {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) :
    Submodule.span E (N : Set (Sp E n)) = ⊤ := by
  classical
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply le_antisymm ?_ bot_le
  intro f hf
  let v : Sp E n := fun i => star (f (Pi.single i 1))
  have hpair : hStd E n v = f := by
    apply (Pi.basisFun E (Fin n)).ext
    intro i
    rw [Pi.basisFun_apply, hStd_apply, Finset.sum_eq_single i]
    · simp [v]
    · intro j _ hj
      simp [hj]
    · simp
  have hline (r : E) : r • v ∈ N := by
    rw [← show dual (hStd E n) N = N from hN.2, dualBasic_mem_dual]
    intro y hy
    have hy0 : hStd E n v y = 0 := by
      rw [hpair]
      exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
    have hz : hStd E n y v = 0 := by
      simpa [hy0] using ((hStd_isSymm (E := E) (n := n)).eq v y).symm
    simp [hz]
  have hv : v = 0 := by
    funext i
    change v i = 0
    by_contra hi
    let coord := (LinearMap.proj i : Sp E n →ₗ[E] E).restrictScalars (𝓞 E)
    have htop : N.map coord = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
    have : Module.Finite (𝓞 E) E := Module.finite_def.mpr (htop ▸ hN.1.fg.map coord)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  rw [Submodule.mem_bot]
  simpa [hv] using hpair.symm


theorem ordSub_eq_ordDet {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)}
    (hN : IsSdLat N) (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.Mem.Chr.ordSub w (GlobalTheory.Mem.Chr.detSub N) = ordDet w N := by
  letI : Submodule.IsLattice E N := hN.1
  have hfull : Submodule.IsFullLattice E N := ⟨span_eq_top_of_isSdLat hN⟩
  apply ordSub_detSub_eq hfull
  apply GlobalTheory.CharValCompare.isFr_frameAt
  first
  | exact GlobalTheory.CharValCompare.exists_isFr w hN
  | exact GlobalTheory.CharValCompare.exists_isFr w hN.1

theorem inv_val_detIdl : ∀ (X : Fields) (n : ℕ) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E))) (χ : Formalism.L2.Host.HChar X.E) (σ : X.K →+* ℂ) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : HeightOneSpectrum (𝓞 X.E) → Sp X.E n ≃ₗ[X.E] Sp X.E n), X.Ok → IsSel X sel → IsSdLat N → χ.TrivOn X.F → (∀ w, w ∉ SB → conjPrime₂ w ∉ SB → χ.UnrAt w ∧ σ ((mU w : X.Kˣ) : X.K) = ((χ.val w : ℂˣ) : ℂ)⁻¹) → ((χ.1 (detIdl SB N fr) : ℂˣ) : ℂ)⁻¹ = σ (muOff sel SB mU N) * ∏ P : SB, ((χ.locK P.1 (LinearEquiv.det (fr P.1)) : ℂˣ) : ℂ)⁻¹ := by
  intro X n sel SB χ σ mU N fr hX hsel hN hT hU
  classical
  set g : HeightOneSpectrum (𝓞 X.E) → ℂˣ := fun w =>
    if w ∈ SB ∨ conjPrime₂ w ∈ SB then 1 else χ.val w ^ (ordDet w N).toNat with hg
  have hfin : (Function.mulSupport g).Finite := by
    refine (GlobalTheory.OrdDetConj.ordDet_conj_finite X.E n N hN).2.subset fun w hw h0 => hw ?_
    simp [hg, h0]
  have h0 : ∀ w, conjPrime₂ w = w → ordDet w N = 0 := fun w hw => by
    have := GlobalTheory.OrdDetConj.ordDet_conjP hN w
    rw [hw] at this
    omega
  have h1 : ∀ w, conjPrime₂ w = w → g w = 1 := fun w hw => by simp [hg, h0 w hw]
  have e1 : χ.1 (detIdl SB N fr) = (∏ P ∈ SB, χ.locK P (LinearEquiv.det (fr P))) * ∏ᶠ w, g w := by
    unfold detIdl
    rw [map_mul, map_prod, MonoidHom.map_finprod _ (finite_detIdl SB hN.1)]
    congr 1
    refine finprod_congr fun w => ?_
    simp only [hg]
    split_ifs
    · exact map_one _
    · rw [map_pow, ordSub_eq_ordDet hN]
      rfl
  have e2 : ∀ v, σ (GlobalTheory.MuOffMove.term sel SB mU N v) = (((g (sel v) * g (conjPrime₂ (sel v)))⁻¹ : ℂˣ) : ℂ) := by
    intro v
    unfold GlobalTheory.MuOffMove.term
    by_cases hc : conjPrime₂ (sel v) = sel v
    · rw [hc, h1 _ hc, h0 _ hc]
      simp
    · obtain ⟨hm, hsp⟩ := GlobalTheory.ThetaMove.split_of_conj_ne₂ X (sel v) v hX hc (hsel v)
      by_cases hv : sel v ∈ SB ∨ conjPrime₂ (sel v) ∈ SB
      · have hv' : ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal :=
          hv.elim (fun h => ⟨_, h, (hsp _).2 (Or.inl rfl)⟩) fun h => ⟨_, h, (hsp _).2 (Or.inr rfl)⟩
        rw [if_pos hv']
        simp only [hg, GlobalTheory.CharValCompare.conjP_conjP]
        rw [if_pos hv, if_pos hv.symm]
        simp
      · have hv' : ¬ ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal := by
          rintro ⟨P, hP, e⟩
          rcases (hsp P).1 e with rfl | rfl
          exacts [hv (Or.inl hP), hv (Or.inr hP)]
        obtain ⟨ha, hb⟩ := not_or.1 hv
        obtain ⟨u1, s1⟩ := hU _ ha hb
        obtain ⟨u2, -⟩ := hU _ hb (by rwa [GlobalTheory.CharValCompare.conjP_conjP])
        rw [if_neg hv']
        simp only [hg, GlobalTheory.CharValCompare.conjP_conjP]
        rw [if_neg hv, if_neg fun h => hv (Or.symm h), GlobalTheory.OrdDetConj.ordDet_conjP hN,
          GlobalTheory.HeckeSplit.val_eq_inv_of_split X.F X.E χ v _ _ hT u1 u2 (Ne.symm hc) hm, pow_toNat_mul,
          Units.val_zpow_eq_zpow_val, map_zpow₀, s1, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, inv_zpow]
  have hinj : Function.Injective sel := fun v w h => HeightOneSpectrum.ext (by rw [← hsel v, h, hsel w])
  have e3 : σ (muOff sel SB mU N) = (((∏ᶠ w, g w)⁻¹ : ℂˣ) : ℂ) := by
    change σ (∏ᶠ v, GlobalTheory.MuOffMove.term sel SB mU N v) = _
    rw [finprod_group hX hsel g hfin h1, ← finprod_inv_distrib,
      map_finprod σ (GlobalTheory.MuOffMove.term_finite hsel SB mU hN), finprod_congr e2]
    exact ((Units.coeHom ℂ).map_finprod_of_injective Units.val_injective
      fun v => (g (sel v) * g (conjPrime₂ (sel v)))⁻¹).symm
  rw [e3, e1, Finset.prod_coe_sort SB fun P => ((χ.locK P (LinearEquiv.det (fr P)) : ℂˣ) : ℂ)⁻¹]
  simp [mul_comm]

end GlobalTheory.DetIdlValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatStepOfChThOk
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

namespace GlobalTheory.KerT

theorem ratStep_of_chTh_ok : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ) (A : Formalism.L2.Ker.Amb X), X.Ok → Pr.Ok → Ch.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ChTh.Ok (Ch := Ch) cst (Formalism.L2.Ker.chTh W Ch sel mu cst A u m2) → i < R.m → GlobalTheory.KerT.RatStep W Ch sel mu cst A u i (i + 1) := by
  intro X Pr R W Ch sel S mu cst L G m2 u i A _ _ _ _ _ _ hL _ hT hi
  have hq := Formalism.L2.Ker.muqTie_of_ok Ch sel mu cst L hL
  have hm := hL.hm
  have key : ∀ j, (j = i + 1 ∧ i ≤ m2) ∨ (j = R.m ∧ i = m2 + 1) → GlobalTheory.KerT.RatStep W Ch sel mu cst A u i j := by
    intro j hj
    unfold RatStep
    rw [← Formalism.L2.Ker.stepC_eq_stepT W Ch sel mu cst hq A u i hi]
    rcases hj with ⟨rfl, h⟩ | ⟨rfl, rfl⟩
    · intro γ γ' N fr N' fr' c x h'
      exact (hT.th i h).equiv γ γ' N fr N' fr' c x h'.1 h'.2.1
    · intro γ γ' N fr N' fr' c x h'
      exact hT.top.equiv γ γ' N fr N' fr' c x h'.1 h'.2.1
  exact key _ (by omega)

end GlobalTheory.KerT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SameOfAbove
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section

namespace GlobalTheory.LvT.Built.UpLaw

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β]
  {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q} {pref : DecoF X.E n ST SG Q → Prop} {T : ℕ} {P : ST}
  (hP : MoveHyp ST SG P) (hT : (T : 𝓞 X.E) ∈ P.1.asIdeal ∧ (T : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
  (hQ : ∀ w : Q, w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1) (hy : y.Off P.1)

include hP hT hQ hy

theorem above_iff (b : β) (p q : PtY ST SG Q y) : Above (tdatY ST T y β Λ Θ pref) b P p q ↔
    p.1.1.deco.1.IsUp P (T : 𝓞 X.E) q.1.1.deco.1 ∧ q.1.1.1.2 = p.1.1.1.2 ∧ q.1.2 = p.1.2 := by
  constructor
  · rintro ⟨x, hx, hf, rfl⟩
    have h := mv_up T p P hP hT hQ hy hx hf
    exact ⟨⟨x, hx, hf, h.1⟩, h.2⟩
  · rintro ⟨⟨x, hx, hf, e⟩, h2, h3⟩
    have h := mv_up T p P hP hT hQ hy hx hf
    exact ⟨x, hx, hf, PtY.ext' (Subtype.ext (e.trans h.1.symm)) (h2.trans h.2.1.symm) (h3.trans h.2.2.symm)⟩

theorem bijOn_up (b : β) (p : PtY ST SG Q y) : Set.BijOn (fun q : PtY ST SG Q y => q.1.1.deco)
    {q | Above (tdatY ST T y β Λ Θ pref) b P p q} {d | p.1.1.deco.1.IsUp P (T : 𝓞 X.E) d.1} := by
  refine ⟨fun q hq => ((above_iff hP hT hQ hy b p q).1 hq).1, fun q hq q' hq' e => ?_, fun d hd => ?_⟩
  · have h := ((above_iff hP hT hQ hy b p q).1 hq).2
    have h' := ((above_iff hP hT hQ hy b p q').1 hq').2
    exact PtY.ext' e (h.1.trans h'.1.symm) (h.2.trans h'.2.symm)
  · obtain ⟨x, hx, hf, e⟩ := hd
    exact ⟨_, ⟨x, hx, hf, rfl⟩, Subtype.ext ((mv_up T p P hP hT hQ hy hx hf).1.trans e.symm)⟩

theorem bijOn_dn (b : β) (p : PtY ST SG Q y) : Set.BijOn (fun q : PtY ST SG Q y => q.1.1.deco)
    {q | Above (tdatY ST T y β Λ Θ pref) b P q p} {d | d.1.IsUp P (T : 𝓞 X.E) p.1.1.deco.1} := by
  refine ⟨fun q hq => ((above_iff hP hT hQ hy b q p).1 hq).1, fun q hq q' hq' e => ?_, fun d hd => ?_⟩
  · have h := ((above_iff hP hT hQ hy b q p).1 hq).2
    have h' := ((above_iff hP hT hQ hy b q' p).1 hq').2
    exact PtY.ext' e (h.1.symm.trans h'.1) (h.2.symm.trans h'.2)
  · have hs := fun w h1 h2 => (Deco.IsUp.sameAt d.2 hP hd (Q := w) h1 h2).localization_eq.symm
    have h := p.mv_spec d (fun w => hs w.1 (hQ w).1 (hQ w).2) (hy _ _ hs)
    refine ⟨p.mv d, (above_iff hP hT hQ hy b _ p).2 ⟨?_, h.2.1.symm, h.2.2.symm⟩, h.1⟩
    rw [h.1]
    exact hd

theorem same_of_above (b : β) {p q : PtY ST SG Q y} (h : Above (tdatY ST T y β Λ Θ pref) b P p q) :
    SameOff ST p.1.1.deco.1.N q.1.1.deco.1.N ∧ p.1.1.deco.1.be = q.1.1.deco.1.be ∧ p.1.1.fr = q.1.1.fr ∧ p.1.2 = q.1.2 := by
  obtain ⟨h1, h2, h3⟩ := (above_iff hP hT hQ hy b p q).1 h
  exact ⟨fun w hw => (h1.sameAt p.1.1.deco.2 hP (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm, h1.be_eq.symm,
    funext fun w => (congrFun h2 w).symm, h3.symm⟩

end Gen

theorem kAt_uk : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Formalism.L2.Ker.Amb X), KerIsTerm W Ch sel mu cst L A u i → GlobalTheory.KerT.UKTerm W Ch sel mu cst A u i (i + 1) → ∀ b b' (d : (stepAt sel mu cst L Tp u i).D b) (d' : (stepAt sel mu cst L Tp u (i + 1)).D b') (P : Pr.vT u) F, (∑ᶠ d₁ ∈ {d₁ | Above (tdatAt sel mu cst L Tp u (i + 1)) b' P d' d₁}, kAt W Ch sel mu cst L A u i b b' d d₁ F) = ((Pr.T u : X.K) ^ ((R.t + 1) / 2)) • ∑ᶠ d₀ ∈ {d₀ | Above (tdatAt sel mu cst L Tp u i) b P d₀ d}, kAt W Ch sel mu cst L A u i b b' d₀ d' F := by
  intro X Pr R W Ch sel S mu cst L G m2 u i hX hPr hsel hS _ Tp A hK hU b b' d d' P F
  obtain ⟨Ξ₀, hb, -, -, -, hk⟩ := hK b b' d d'
  have hP := moveHyp_of_ok hPr u P
  have hT := T_unif hX hPr u P
  have hQ0 := T_notMem_QE sel mu u hPr hsel hS
  have hQ : ∀ w : QE sel (mu : Chr X.F X.E X.K), w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1 :=
    fun w => ne_of_T_notMem hPr u P (hQ0 w.1 w.2)
  have hy := fun j => ysAt_off (R := R) sel mu cst hPr u hQ0 j P
  have refl : ∀ {j : ℕ} (p : PtAt R sel mu cst u j), SameOffPt sel mu cst u p p :=
    fun p => ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  have key := hU d.1.1.deco (frsF sel mu d.1.1) d'.1.1.deco (frsF sel mu d'.1.1) Ξ₀ P F hP hP hb
  refine (finsum_mem_eq_of_bijOn _ (bijOn_up hP hT hQ (hy (i + 1)) b' d') fun q hq => ?_).trans
    (key.trans (congrArg _ (finsum_mem_eq_of_bijOn _ (bijOn_dn hP hT hQ (hy i) b d) fun q hq => ?_).symm))
  · rw [hk d q (refl d) (same_of_above hP hT hQ (hy (i + 1)) b' hq)]
  · obtain ⟨h1, h2, h3, h4⟩ := same_of_above hP hT hQ (hy i) b hq
    rw [hk q d' ⟨fun w hw => (h1 w hw).symm, h2.symm, h3.symm, h4.symm⟩ (refl d')]

end GlobalTheory.LvT.Built.UpLaw
end
end

