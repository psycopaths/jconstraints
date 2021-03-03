/*
 * Copyright 2020 TU Dortmund, Malte Mues
 */

import org.gradle.api.tasks.testing.logging.TestLogEvent.*
plugins {
    `java-library`
    `maven-publish`
    id("com.github.hierynomus.license") version "0.15.0"
    id("com.github.sherter.google-java-format") version "0.9"
    id("com.github.johnrengelman.shadow") version "5.2.0"
}

repositories {
    jcenter()
    mavenLocal()
    mavenCentral()
}

group = "tools.aqua"
version = "0.9.6-SNAPSHOT"
description = "JConstraints-z3"

dependencies {
    implementation("com.google.guava:guava:30.1-jre")
    implementation("io.github.tudo-aqua:z3-turnkey:4.8.10")
    implementation("tools.aqua:jconstraints:0.9.6-SNAPSHOT")

    testImplementation("org.testng:testng:7.0.0")
}

java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(8))
    }
}

val test by tasks.getting(Test::class) {
    useTestNG() {
        useDefaultListeners = true
    }
    testLogging {
        events(FAILED, STANDARD_ERROR, SKIPPED, PASSED)
    }
}


tasks.shadowJar {
    //FIXME: Exclude the other jconstraints-deps
    exclude("tools.aqua:jconstraints:.*")
    archiveFileName.set(
        "${archiveBaseName.get()}-${archiveClassifier.get()}-${archiveVersion.get()}.${archiveExtension.get()}"
    )
}

license {
    header = rootProject.file("NOTICE")
    strictCheck = true
}

publishing {
    publications {
        create<MavenPublication>("mavenJava") {
            artifactId = "jconstraints-z3"
            from(components["java"])
            pom {
                name.set("jConstraints-z3")
                description.set("JConstraints-Z3 is the Z3 API plug-in for JConstraints.")
                url.set("https://github.com/tudo-aqua/jconstraints-z3")
                licenses {
                    license {
                        name.set("Apache-2.0")
                        url.set("https://www.apache.org/licenses/LICENSE-2.0.txt")
                    }
                }
                developers {
                    developer {
                        id.set("mmuesly")
                        name.set("Malte Mues")
                        email.set("mail.mues@gmail.com")
                    }
                    developer {
                        id.set("fhowar")
                        name.set("Falk Howar")
                    }
                }
                scm {
                    connection.set("https://github.com/tudo-aqua/jconstraints-z3")
                    url.set("https://github.com/tudo-aqua/jconstraints-z3")
                }
            }
        }
        create<MavenPublication>("publishMaven") {
            artifact(tasks["shadowJar"]) {
                classifier = null
            }
            artifactId = "jconstraints-z3-all"

        }
    }
}
