using Microsoft.VisualStudio.TestTools.UnitTesting;
using Microsoft.Dafny;
using System.IO;
using System;

namespace DafnyInfoFlowTest
{
    public class Util
    {
        internal static bool CompareFiles(string file1, string file2)
        {
            byte[] bytes1 = File.ReadAllBytes(file1);
            byte[] bytes2 = File.ReadAllBytes(file2);

            if (bytes1.Length == bytes2.Length)
            {
                byte file1Byte = 0;
                byte file2Byte = 0;
                for (var i = 0; i < bytes1.Length; i++)
                {
                    file1Byte = bytes1[i];
                    file2Byte = bytes2[i];
                    if (!(file1Byte == file2Byte)) {
                        Console.WriteLine("Not equal: " + file1Byte + " | " + file2Byte);
                        return false;
                    }
                }
                return true;
            }
            Console.WriteLine("Different size files");
            return false;
        }
    }

    [TestClass]
    public class FileCompareTest { 
        [TestMethod]
        public void TestSameFile()
        {
            var file1 = Path.GetFullPath("testFiles/fileTest.dfy");
            var file2 = Path.GetFullPath("testFiles/fileTest.dfy");            
            Assert.IsTrue(Util.CompareFiles(file1, file2));
        }

        [TestMethod]
        public void TestDifferentFileSameSizeNotSame()
        {
            var file1 = Path.GetFullPath("testFiles/fileTest.dfy");
            var file2 = Path.GetFullPath("testFiles/sameSizeDiffText.dfy");
            Assert.IsFalse(Util.CompareFiles(file1, file2));
        }

        [TestMethod]
        public void TestDifferentFileSameSizeSame()
        {
            var file1 = Path.GetFullPath("testFiles/fileTest.dfy");
            var file2 = Path.GetFullPath("testFiles/sameSizeDiffTextSame.dfy");
            Assert.IsTrue(Util.CompareFiles(file1, file2));
        }

        [TestMethod]
        public void TestDifferentFileDifferentSize()
        {
            var file1 = Path.GetFullPath("testFiles/fileTest.dfy");
            var file2 = Path.GetFullPath("testFiles/addLabelSoln.dfy");
            Assert.IsFalse(Util.CompareFiles(file1, file2));
        }
    }


    [TestClass]
    public class ASTInjectionTests
    {
        // Default blank file, don't compile, print the code to the output file when done. Don't print command line args at top of file
        string[] args = { "testFiles/", "-compile:0", "-dprint:testFiles/", "-env:0" };
        
        [TestMethod]
        public void TestAddLabels()
        {
            var testFile = "addLabelTest.dfy";
            var outFile = "addLabelOut.dfy";
            var solnFile = "testFiles/addLabelSoln.dfy";
            
            args[0] += testFile;
            args[2] += outFile;            
            int result = DafnyDriver.Main(args);
            Assert.IsTrue(result == 0);
            Assert.IsTrue(Util.CompareFiles("testFiles/" + outFile, solnFile));
        }

        [TestMethod]
        public void TestAddLabelIf()
        {
            var testFile = "addLabelIfTest.dfy";
            var outFile = "addLabelIfOut.dfy";
            var solnFile = "testFiles/addLabelIfSoln.dfy";

            args[0] += testFile;
            args[2] += outFile;
            int result = DafnyDriver.Main(args);
            //Assert.IsTrue(result == 0);

            Assert.IsTrue(Util.CompareFiles("testFiles/" + outFile, solnFile));
        }

        [TestMethod]
        public void TestAddManyLabels()
        {
            var testFile = "addManyLabelsTest.dfy";
            var outFile = "addManyLabelsOut.dfy";
            var solnFile = "testFiles/addManyLabelsSoln.dfy";

            args[0] += testFile;
            args[2] += outFile;
            int result = DafnyDriver.Main(args);
            Assert.IsTrue(result == 0);

            Assert.IsTrue(Util.CompareFiles("testFiles/" + outFile, solnFile));
        }

        [TestMethod]
        public void TestAddWhileLabels()
        {
            var testFile = "addLabelWhileTest.dfy";
            var outFile = "addLabelWhileOut.dfy";
            var solnFile = "testFiles/addLabelWhileSoln.dfy";

            args[0] += testFile;
            args[2] += outFile;
            DafnyDriver.Main(args);

            Assert.IsTrue(Util.CompareFiles("testFiles/" + outFile, solnFile));
        }

        [TestMethod]
        public void TestAddClassLabels()
        {
            var testFile = "addLabelClassTest.dfy";
            var outFile = "addLabelClassOut.dfy";
            var solnFile = "testFiles/addLabelClassSoln.dfy";

            args[0] += testFile;
            args[2] += outFile;
            DafnyDriver.Main(args);

            Assert.IsTrue(Util.CompareFiles("testFiles/" + outFile, solnFile));
        }

        [TestMethod]
        public void TestAddSimultaneousLabels()
        {
            var testFile = "addLabelSimultaneousTest.dfy";
            var outFile = "addLabelSimultaneousOut.dfy";
            var solnFile = "testFiles/addLabelSimultaneousSoln.dfy";

            args[0] += testFile;
            args[2] += outFile;
            DafnyDriver.Main(args);

            Assert.IsTrue(Util.CompareFiles("testFiles/" + outFile, solnFile));
        }
    }
}
