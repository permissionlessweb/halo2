use super::circuit::{Any, Column};
use crate::{
    arithmetic::CurveAffine,
    poly::{Coeff, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial},
};

use crate::helpers::CurveRead;
use std::io;

pub(crate) mod keygen;
pub(crate) mod prover;
pub(crate) mod verifier;

/// A permutation argument.
#[derive(Debug, Clone)]
pub(crate) struct Argument {
    /// A sequence of columns involved in the argument.
    columns: Vec<Column<Any>>,
}

impl Argument {
    pub(crate) fn new() -> Self {
        Argument { columns: vec![] }
    }

    /// Returns the minimum circuit degree required by the permutation argument.
    /// The argument may use larger degree gates depending on the actual
    /// circuit's degree and how many columns are involved in the permutation.
    pub(crate) fn required_degree(&self) -> usize {
        // degree 2:
        // l_0(X) * (1 - z(X)) = 0
        //
        // We will fit as many polynomials p_i(X) as possible
        // into the required degree of the circuit, so the
        // following will not affect the required degree of
        // this middleware.
        //
        // (1 - (l_last(X) + l_blind(X))) * (
        //   z(\omega X) \prod (p(X) + \beta s_i(X) + \gamma)
        // - z(X) \prod (p(X) + \delta^i \beta X + \gamma)
        // )
        //
        // On the first sets of columns, except the first
        // set, we will do
        //
        // l_0(X) * (z(X) - z'(\omega^(last) X)) = 0
        //
        // where z'(X) is the permutation for the previous set
        // of columns.
        //
        // On the final set of columns, we will do
        //
        // degree 3:
        // l_last(X) * (z'(X)^2 - z'(X)) = 0
        //
        // which will allow the last value to be zero to
        // ensure the argument is perfectly complete.

        // There are constraints of degree 3 regardless of the
        // number of columns involved.
        3
    }

    pub(crate) fn add_column(&mut self, column: Column<Any>) {
        if !self.columns.contains(&column) {
            self.columns.push(column);
        }
    }

    pub(crate) fn get_columns(&self) -> Vec<Column<Any>> {
        self.columns.clone()
    }

    /// Write permutation argument to binary format.
    ///
    /// Format:
    /// - [num_columns: u16 LE]
    /// - For each column: [column_type: u8][column_index: u16 LE]
    pub fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&(self.columns.len() as u16).to_le_bytes())?;
        for column in &self.columns {
            let (col_type, col_index) = match column.column_type() {
                Any::Fixed => (0u8, column.index()),
                Any::Advice => (1u8, column.index()),
                Any::Instance => (2u8, column.index()),
            };
            writer.write_all(&[col_type])?;
            writer.write_all(&(col_index as u16).to_le_bytes())?;
        }
        Ok(())
    }

    /// Read permutation argument from binary format.
    pub fn read<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        let mut len_bytes = [0u8; 2];
        reader.read_exact(&mut len_bytes)?;
        let num_columns = u16::from_le_bytes(len_bytes) as usize;

        let mut columns = Vec::with_capacity(num_columns);
        for _ in 0..num_columns {
            let mut col_type_byte = [0u8; 1];
            reader.read_exact(&mut col_type_byte)?;
            let mut col_index_bytes = [0u8; 2];
            reader.read_exact(&mut col_index_bytes)?;
            let col_index = u16::from_le_bytes(col_index_bytes) as usize;

            let column: Column<Any> = match col_type_byte[0] {
                0 => Column::new(col_index, Any::Fixed),
                1 => Column::new(col_index, Any::Advice),
                2 => Column::new(col_index, Any::Instance),
                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!("Invalid permutation column type: {}", col_type_byte[0]),
                    ))
                }
            };
            columns.push(column);
        }

        Ok(Argument { columns })
    }
}

/// The verifying key for a single permutation argument.
#[derive(Clone, Debug)]
pub(crate) struct VerifyingKey<C: CurveAffine> {
    commitments: Vec<C>,
}


impl<C: CurveAffine> VerifyingKey<C> {
    pub(crate) fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(&(u32::try_from(self.commitments.len()).unwrap()).to_le_bytes())?;
        for commitment in &self.commitments {
            writer.write_all(commitment.to_bytes().as_ref())?;
        }
        Ok(())
    }
    pub(crate) fn read<R: io::Read>(reader: &mut R, argument: &Argument) -> io::Result<Self> {
        let mut num_commitments_le_bytes = [0u8; 4];
        reader.read_exact(&mut num_commitments_le_bytes)?;
        let num_commitments = u32::from_le_bytes(num_commitments_le_bytes);
        eprintln!("argument.columns.len(): {}", argument.columns.len());
        eprintln!("num_commitments: {}", num_commitments);
        eprintln!("argument: {:#?}", argument);

        let expected = num_commitments as usize;
        if argument.columns.len() != expected {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "unexpected number of column commitments: expected {}, got {}",
                    expected,
                    argument.columns.len()
                ),
            ));
        }
        let commitments: Vec<_> = (0..argument.columns.len())
            .map(|_| C::read(reader))
            .collect::<io::Result<_>>()?;
        Ok(VerifyingKey { commitments })
    }
    pub(crate) fn bytes_length(&self) -> usize {
        4 + self.commitments.len() * C::default().to_bytes().as_ref().len()
    }
}


/// The proving key for a single permutation argument.
#[derive(Clone, Debug)]
pub(crate) struct ProvingKey<C: CurveAffine> {
    permutations: Vec<Polynomial<C::Scalar, LagrangeCoeff>>,
    polys: Vec<Polynomial<C::Scalar, Coeff>>,
    pub(super) cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
}
